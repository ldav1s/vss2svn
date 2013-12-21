#!/usr/bin/perl

use warnings;
use strict;

use v5.10.1;

use feature "switch";
use feature "state";

use Cwd 'abs_path';
use Getopt::Long;
use Data::UUID;
use DBI;
use DBD::SQLite;
use Hash::Case::Preserve;
use XML::LibXML;
use File::Basename;
use File::Copy;
use File::Find;
use File::Path qw(make_path rmtree);
use File::Spec;
use IPC::Run qw( run );
use Time::CTime;
use Benchmark ':hireswallclock';
use Fcntl ':mode';
use Storable qw(dclone nfreeze thaw);
use Term::ProgressBar;

use lib '.';
use POSIX;
use Git::Repository qw( +Vss2Svn2Git::GitLogger );
use Data::Dumper;
use version; our $VERSION = version->declare("v0.90.0");

# task names for conversion states
use constant {
    TASK_INIT => 'INIT',
    TASK_LOADVSSNAMES => 'LOADVSSNAMES',
    TASK_FINDDBFILES => 'FINDDBFILES',
    TASK_GETPHYSHIST => 'GETPHYSHIST',
    TASK_REMOVETMPCHECKIN => 'REMOVETMPCHECKIN',
    TASK_FIXUPPARENT => 'FIXUPPARENT',
    TASK_TESTGITAUTHORINFO => 'TESTGITAUTHORINFO',
    TASK_GITREAD => 'GITREAD',
    TASK_GITLABEL => 'GITLABEL',
    TASK_CLEANUP => 'CLEANUP',
    TASK_DONE => 'DONE',
};

# other constants
use constant {
    SSPHYS => 'ssphys',
    TEMPDIR => '_vss2svn2git',
    REPO => 'repo',
    REVTIMERANGE => 3600,
    ENCODING => 'windows-1252',
    VSS_PROJECT => 1,
    VSS_FILE => 2,
    BRANCH_TMP_FILE => '.vss2svn2gitbranchtmp',
    MOVE_TMP_FILE => '.vss2svn2gitmovetmp',
    KEEP_FILE => '.vss2svn2gitkeep',
    VSS2SVN2GIT_NS => 'ns:vss2svn2git',
    PROGNAME => 'vss2svn2git',
    PROGNAME_URL => 'https://github.com/ldav1s/vss2svn',
    VSSDB_ROOT => 'AAAAAAAA',
    ISO8601_FMT => '%Y-%m-%dT%H:%M:%S',
    MINMAX_TIME_FMT => '%Y-%m-%d',
    # This is arbitrary, tried to keep it fairly small
    PAIR_INSERT_VAL => 256,
    # This is arbitrary, tried to keep it fairly small
    PHYSICAL_FILES_LIMIT => 512,
    # This is arbitrary, tried to keep it fairly small
    PA_PARAMS_LIMIT => 16,
    # This is arbitrary, tried to keep it really small
    TIMESTAMP_DELTA => 4,
};

# values for prioritizing actions within a timestamp
use constant {
    PA_PRIORITY_MAX => 1, # highest priority
    PA_PRIORITY_ADD => 1,
    PA_PRIORITY_SHARE => 2,
    PA_PRIORITY_PIN => 2,
    PA_PRIORITY_BRANCH => 3,
    PA_PRIORITY_NORMAL => 5,
    PA_PRIORITY_DELETE => 7,
    PA_PRIORITY_DESTROY => 8,
    PA_PRIORITY_MIN => 8, # minimum priority
};

# actions used in actiontype database column
use constant {
    ACTION_ADD => 'ADD',
    ACTION_RESTOREDPROJECT => 'RESTOREDPROJECT',
    ACTION_RENAME => 'RENAME',
    ACTION_MOVE_TO => 'MOVE_TO',
    ACTION_MOVE_FROM => 'MOVE_FROM',
    ACTION_DELETE => 'DELETE',
    ACTION_DESTROY => 'DESTROY',
    ACTION_RECOVER => 'RECOVER',
    ACTION_RESTORE => 'RESTORE',
    ACTION_COMMIT => 'COMMIT',
    ACTION_SHARE => 'SHARE',
    ACTION_BRANCH => 'BRANCH',
    ACTION_PIN => 'PIN',
    ACTION_LABEL => 'LABEL',
};

our(%gCfg, %gErr, $gSysOut);

# The git image is the physical layout of files in the git repo
# that get built up as we step through history.
# The git_image hash maps from VSS physname to hard link list for VSS_FILEs:
# (e.g. 'MBAAAAAA' => ('/some/repo/file', '/some/repo/somewhere/shared-file')).
# The link to "$gCfg{links}/MBAAAAAA" is implicit.
# The image is physname to path (e.g. 'XBAAAAAA' => '/some/repo/dir') for
# VSS_PROJECT.
my %git_image = ();

# Label map is a map from VSS label names to the corresponding git branch name
# (e.g. 'My VSS Label' => 'My_VSS_Label').  If the label is undef, a
# unique name will be generated for it (and not added here).  If the label is
# defined but the branch name algorithm fails to generate a "fixed up" version
# it will also be given a generated name and stored here.
# N.B. This must be case insensitive since VSS treats labels case insenstively
my $label_map = {};
tie %{$label_map}, 'Hash::Case::Preserve';

# destroyed_files tracks the active destroyed fill-in files by physname
my $destroyed_files = {};

# The author map maps VSS author information to git author information
my $author_map = {};

# The main VSS activity is put into git master, and labels into their own branch
my $master_re = qr/^master$/i;

# A regex for the repo directory
my $repo_re;

# store a hash of actions to take; allows restarting in case of failed
# migration
my @joblist =
    (
     {
         task    => TASK_INIT,
         handler => sub{ $gCfg{resume} = 0; 1; },
     },
     # Load the "real" names associated with the stored "short" names
     {
         task => TASK_LOADVSSNAMES,
         handler => \&LoadVssNames,
     },
     # Add a stub entry into the Physical table for each physical
     # file in the VSS DB
     {
         task => TASK_FINDDBFILES,
         handler => \&FindPhysDbFiles,
     },
     # Load the history of what happened to the physical files. This
     # only gets us halfway there because we don't know what the real
     # filenames are yet
     {
         task => TASK_GETPHYSHIST,
         handler => \&GetPhysVssHistory,
     },
     # Remove temporary check ins
     {
         task => TASK_REMOVETMPCHECKIN,
         handler => \&RemoveTemporaryCheckIns,
     },
     # Test git author data
     {
         task => TASK_TESTGITAUTHORINFO,
         handler => \&TestGitAuthorInfo,
     },
     # Fix up ACTION_ADD, ACTION_BRANCH comments
     {
         task => TASK_FIXUPPARENT,
         handler => \&FixupParentActions,
     },
     # Read in the master branch for git converting the history
     # into the master branch.
     {
         task => TASK_GITREAD,
         handler => \&GitReadImage,
     },
     # Replay the labels
     {
         task => TASK_GITLABEL,
         handler => \&ReplayLabels,
     },
     # Clean up
     {
         task => TASK_CLEANUP,
         handler => \&Cleanup,
     },
     # done state
     {
         task    => TASK_DONE,
         handler => sub { 1; },
     }
    );

# Data for PhyicalAction table
my @physical_action_params = (
    { 'physname' =>    'VARCHAR' },
    { 'version' =>     'INTEGER' },
    { 'parentphys' =>  'VARCHAR' },
    { 'actiontype' =>  'VARCHAR' },
    { 'itemname' =>    'VARCHAR' },
    { 'timestamp' =>   'INTEGER' },
    { 'author' =>      'VARCHAR' },
    { 'info' =>        'VARCHAR' },
    { 'priority' =>    'INTEGER' },
    { 'parentdata' =>  'INTEGER' },
    { 'comment' =>     'TEXT' },
    );

# Data for SystemInfo table
my @system_info_params = (
    { 'task' =>    'VARCHAR' },
    { 'ssphys' =>  'VARCHAR' },
    { 'tempdir' => 'VARCHAR' },
    { 'starttime' => 'VARCHAR' },
    { 'gpvh_physname' => 'VARCHAR' }, # checkpoint for GetPhysVssHistory
    { 'gri_git_head' => 'VARCHAR' }, # checkpoints for GetReadImage
    { 'gri_timestamp' => 'INTEGER' },
    { 'gri_next_update' => 'INTEGER' },
    { 'gri_git_image' => 'TEXT' },
    { 'gri_destroyed_files' => 'TEXT' },
    { 'gri_exclude' => 'TEXT' },
    { 'rl_next_update' => 'INTEGER' }, # checkpoints for ReadLabel
    { 'rl_label_map' => 'TEXT' },
    );

&Initialize;
&ConnectDatabase;

&SetupGlobals;
&ShowHeader;

&RunConversion;

&ShowSummary;
&DisconnectDatabase;

###############################################################################
#  RunConversion
###############################################################################
sub RunConversion {


    my $taskmap = {};
    my $i = 0;
    my $task_name_sz = 0;

    foreach my $e (@joblist) {
        $taskmap->{$e->{task}} = $i++;
        $task_name_sz = length($e->{task}) if length($e->{task}) > $task_name_sz;
    }

    die "FATAL ERROR: Unknown task '$gCfg{task}'\n"
        unless defined $taskmap->{$gCfg{task}};

    for ($i = $taskmap->{$gCfg{task}}; $i <= $taskmap->{"@{[TASK_DONE]}"}; ++$i) {
        $gCfg{current_task} = $joblist[$i];
        $gCfg{next_task} = ($i != $taskmap->{"@{[TASK_DONE]}"}) ? $joblist[$i+1] : $joblist[$i];

        &SetSystemTask( $gCfg{current_task}->{task} );
        say sprintf("TASK: %*s: %s", $task_name_sz, $gCfg{task},
                    POSIX::strftime(ISO8601_FMT . "\n", localtime));

        if ($gCfg{prompt}) {
            say "Press ENTER to continue or 'quit' to quit...";
            my $temp = <STDIN>;
            die if $temp =~ m/^quit/i;
        }

        if ($i >= $taskmap->{"@{[TASK_GITREAD]}"}) {
            if (!defined $gCfg{mintime} && !defined $gCfg{maxtime}) {
                &TimestampLimits;
                if (!defined $gCfg{mintime} || !defined $gCfg{maxtime}) {
                    warn "There doesn't seem to be any physical action data";
                }
            }
            if (!defined $gCfg{destroyedHash}) {
                &DestroyedHash;
            }
        }

        &{ $gCfg{current_task}->{handler} };
    }

}  #  End RunConversion

###############################################################################
#  LoadVssNames
###############################################################################
sub LoadVssNames {
    my @cmd = ('info', "-e$gCfg{encoding}",
               File::Spec->catdir($gCfg{vssdatadir}, 'names.dat'));
    &DoSsCmd(@cmd);

    $gCfg{resume} = 0;

    $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
    eval {
        my $xmldoc = XML::LibXML->load_xml(string => $gSysOut);

        # The cache can contain 4 different entries:
        #   id=1: abbreviated DOS 8.3 name for file items
        #   id=2: full name for file items
        #   id=3: abbreviated 27.3 name for file items
        #   id=10: full name for project items
        # Both ids 1 and 3 are not of any interest for us, since they only
        # provide abbreviated names for different scenarios. We are only
        # interested if we have id=2 for file items, or id=10 for project
        # items.
        my $interest = 'Entry[@id = 2 or @id = 10]'; # XPath query for Entries of interest
        my @namecacheentries = $xmldoc->findnodes("File/NameCacheEntry[$interest]"); # XPath for grabbing the enclosing NameCacheEntry
        my @val_list = ();

        # all the NameCacheEntries should be valid, now filter Entries
        foreach my $namecachentry (@namecacheentries) {
            my $offset = $namecachentry->getAttribute('offset');
            my @entries = $namecachentry->findnodes($interest);
            foreach my $entry (@entries) {
                my $name = $entry->textContent();
                push @val_list, $offset, $name;
            }

            if (scalar @val_list >= PAIR_INSERT_VAL) {
                &LoadUpVssNames(\@val_list);
                @val_list = ();
            }
        }

        if (scalar @val_list > 0) {
            &LoadUpVssNames(\@val_list);
            @val_list = ();
        }
    };

    if ($@) {
        warn "Transaction aborted because $@";
        eval { $gCfg{dbh}->rollback };
        die "Failed to load name lookup table";
    } else {
        &SetSystemTask( $gCfg{next_task}->{task} );
        $gCfg{dbh}->commit;
    }

    1;
}  #  End LoadVssNames

sub LoadUpVssNames {
    my($val_list) = @_;

    my $val_clause = join q{,}, ('(?, ?)') x ((scalar @{$val_list})/2);
    my $sth = $gCfg{dbh}->prepare("INSERT INTO NameLookup (offset, name) VALUES $val_clause");
    $sth->execute(@{$val_list});
}

###############################################################################
#  FindPhysDbFiles
###############################################################################
sub FindPhysDbFiles {

    my $sth = $gCfg{dbh}->prepare("INSERT INTO Physical (physname, datapath) VALUES (?, ?)");

    $gCfg{resume} = 0;

    $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
    eval {
        my $vssdb_cnt = 0;
        my @dirs = ($gCfg{vssdatadir});
        my $start_depth = $gCfg{vssdatadir} =~ tr[/][];
        my $vssfile_depth = $start_depth + 1;

        find({
            preprocess => sub {
                my $depth = $File::Find::dir =~ tr[/][];
                return sort grep { -d $_ && $_ =~ m:^[a-z]{1}$:i } @_ if $depth < $vssfile_depth;
                return sort grep { -f $_ && $_ =~ m:^[a-z]{8}$:i } @_ if $depth == $vssfile_depth;
            },
            wanted => sub {
                my $depth = $File::Find::dir =~ tr[/][];
                return if $depth != $vssfile_depth;
                $sth->execute(uc($_), $File::Find::name);
                ++$vssdb_cnt;
            },
             }, @dirs);
        say "Found $vssdb_cnt VSS database files at '$gCfg{vssdatadir}'" if $gCfg{verbose};
    };

    if ($@) {
        warn "Transaction aborted because $@";
        eval { $gCfg{dbh}->rollback };
        die "Failed to load physical table";
    } else {
        &SetSystemTask( $gCfg{next_task}->{task} );
        $gCfg{dbh}->commit;
    }

    1;
}  #  End FindPhysDbFiles

###############################################################################
#  GetPhysVssHistory
###############################################################################
sub GetPhysVssHistory {

    my $physname = '';
    my $limcount = 0;

    my ($phys_count) = $gCfg{dbh}->selectrow_array('SELECT COUNT(*) FROM Physical');
    my $prg_cnt = 0;
    my $progress;
    my $next_update = 0;

    if ($gCfg{resume}) {
        # back up to last transaction checkpoint
        $physname = $gCfg{gpvh_physname};
        ($prg_cnt) = $gCfg{dbh}->selectrow_array('SELECT COUNT(*) FROM Physical WHERE physname <= ?', undef, $physname);
        $gCfg{resume} = 0;
    }

    if (!($gCfg{debug} || $gCfg{verbose})) {
        $progress = Term::ProgressBar->new({name  => 'VSS History',
                                            count => $phys_count,
                                            ETA   => 'linear', });
        $progress->max_update_rate(1);
    }

    # Break up inserts into multiple transactions
    # Most files have one insert only (and most one set of VALUES only)!
    my $sth = $gCfg{dbh}->prepare("SELECT * FROM Physical "
                               . "WHERE physname > ? "
                               . "ORDER BY physname LIMIT @{[PHYSICAL_FILES_LIMIT]}");
    my $pt_sth = $gCfg{dbh}->prepare('INSERT OR IGNORE INTO PhysItemtype (physname, itemtype) VALUES (?, ?)');
    my $b_sth = $gCfg{dbh}->prepare('INSERT INTO FileBinary (physname, is_binary) VALUES (?, ?)');
    my $li_sth = $gCfg{dbh}->prepare('INSERT INTO PhysLabel (action_id, label) VALUES (?, ?)');
    my $cp_sth = $gCfg{dbh}->prepare('UPDATE SystemInfo SET gpvh_physname = ?');

    my $pa_sth;
    {
        my @pa_ary;
        foreach my $param (@physical_action_params) {
            push @pa_ary, keys %$param;
        }
        my $pa_params_sql = join q{,}, @pa_ary;
        my $val_params = join q{,}, ('?') x (scalar @pa_ary);
        $pa_sth = $gCfg{dbh}->prepare("INSERT INTO PhysicalAction (action_id, $pa_params_sql) VALUES (NULL, $val_params)");
    }

    do {
        $sth->execute($physname);

        $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
        $limcount = 0;
        eval {
            my $row;
            while (defined($row = $sth->fetchrow_hashref() )) {
                $physname = $row->{physname};
                &GetVssPhysInfo($row->{datapath}, $physname, $pa_sth, $pt_sth, $b_sth, $li_sth);
                ++$limcount;
            }
        };
        if ($@) {
            warn "Transaction aborted because $@";
            eval { $gCfg{dbh}->rollback };
            die "Failed to load VSS items for `$physname'";
        } else {
            $cp_sth->execute($physname);
            $gCfg{dbh}->commit;
        }

        $prg_cnt += $limcount;
        if (defined $progress) {
            $next_update = $progress->update($prg_cnt)
                if $prg_cnt > $next_update || $prg_cnt == $phys_count;
        }
    } while ($limcount == PHYSICAL_FILES_LIMIT);

    1;
}  #  End GetPhysVssHistory

###############################################################################
#  GetVssPhysInfo
###############################################################################
sub GetVssPhysInfo {
    my($datapath, $physname, $pa_sth, $pt_sth, $b_sth, $li_sth) = @_;

    say "datapath: \"$datapath\"" if $gCfg{debug};
    my @cmd = ('info', "-e$gCfg{encoding}", "$datapath");
    &DoSsCmd(@cmd);


    my $xmldoc = XML::LibXML->load_xml(string => $gSysOut);

    my $parentphys;

    my $type = $xmldoc->findvalue('File/ItemInfo/Type');
    my $binary = $xmldoc->findvalue('File/ItemInfo/Binary');

    if (!defined $type) {
        &ThrowWarning("Can't handle file '$physname'; not a project or file\n");
        return;
    }

    my @versions = $xmldoc->findnodes('File/Version');

    for ($type+0) {
        when (VSS_PROJECT) {
            $parentphys = $xmldoc->findvalue('File/ItemInfo/ParentPhys');
        }
        when (VSS_FILE) {
            $parentphys = undef;
            $b_sth->execute(uc($physname), $binary);
        }
        default {
            &ThrowWarning("Can't handle file '$physname'; not a project or file\n");
            return;
        }
    }
    $pt_sth->execute(uc($physname), $type+0);

    if (scalar @versions > 0) {
        &GetVssItemVersions($physname, $parentphys, \@versions, $type, $pa_sth, $pt_sth, $li_sth);
    }

}  #  End GetVssPhysInfo

###############################################################################
#  GetVssItemVersions
###############################################################################
sub GetVssItemVersions {
    my($physname, $parentphys, $versions, $ii_type, $pa_sth, $pt_sth, $li_sth) = @_;

    my($parentdata, $version, $vernum, $actionid, $actiontype,
       $tphysname, $itemname, $itemtype, $parent, $user, $timestamp, $comment,
       $info, $priority, $label, $cachename);

    my $last_timestamp = 0;
    # RollBack is only seen in combiation with a BranchFile activity, so actually
    # RollBack is the item view on the activity and BranchFile is the parent side
    # ==> map RollBack to BRANCH, so that we can join the two actions in the
    # MergeParentData step
    # RestoredProject seems to act like CreatedProject, except that the
    # project was recreated from an archive file, and its timestamp is
    # the time of restoration. Timestamps of the child files retain
    # their original values.
    my %gActionType = (
        CreatedProject => {type => VSS_PROJECT, action => ACTION_ADD},
        AddedProject => {type => VSS_PROJECT, action => ACTION_ADD},
        RestoredProject => {type => VSS_PROJECT, action => ACTION_RESTOREDPROJECT},
        RenamedProject => {type => VSS_PROJECT, action => ACTION_RENAME},
        MovedProjectTo => {type => VSS_PROJECT, action => ACTION_MOVE_TO},
        MovedProjectFrom => {type => VSS_PROJECT, action => ACTION_MOVE_FROM},
        DeletedProject => {type => VSS_PROJECT, action => ACTION_DELETE},
        DestroyedProject => {type => VSS_PROJECT, action => ACTION_DESTROY},
        RecoveredProject => {type => VSS_PROJECT, action => ACTION_RECOVER},
        ArchiveProject => {type => VSS_PROJECT, action => ACTION_DELETE},
        RestoredProject => {type => VSS_PROJECT, action => ACTION_RESTORE},
        ArchiveVersionsofProject => {type => VSS_PROJECT, action => ACTION_ADD},
        CheckedIn => {type => VSS_FILE, action => ACTION_COMMIT},
        CreatedFile => {type => VSS_FILE, action => ACTION_ADD},
        AddedFile => {type => VSS_FILE, action => ACTION_ADD},
        RenamedFile => {type => VSS_FILE, action => ACTION_RENAME},
        DeletedFile => {type => VSS_FILE, action => ACTION_DELETE},
        DestroyedFile => {type => VSS_FILE, action => ACTION_DESTROY},
        RecoveredFile => {type => VSS_FILE, action => ACTION_RECOVER},
        ArchiveVersionsofFile => {type => VSS_FILE, action => ACTION_ADD},
        ArchiveFile => {type => VSS_FILE, action => ACTION_DELETE},
        RestoredFile => {type => VSS_FILE, action => ACTION_RESTORE},
        SharedFile => {type => VSS_FILE, action => ACTION_SHARE},
        BranchFile => {type => VSS_FILE, action => ACTION_BRANCH},
        PinnedFile => {type => VSS_FILE, action => ACTION_PIN},
        RollBack => {type => VSS_FILE, action => ACTION_BRANCH},
        UnpinnedFile => {type => VSS_FILE, action => ACTION_PIN},
        Labeled => {type => $ii_type, action => ACTION_LABEL},
        );

    my $namelookup = $gCfg{dbh}->selectall_hashref('SELECT offset, name FROM NameLookup',
                                                   'offset');
VERSION:
    foreach $version (@$versions) {
        $tphysname = $version->exists('Action/Physical')
            ? $version->findvalue('Action/Physical')
            : $physname;
        $user = $version->findvalue('UserName');
        $vernum = $version->findvalue('VersionNumber');
        $timestamp = $version->findvalue('Date');

        $actionid = $version->findvalue('Action/@ActionId');
        $info = $gActionType{$actionid};

        if (!$info) {
            &ThrowWarning ("'$physname': Unknown action '$actionid'\n");
            next VERSION;
        }

        # check the linear order of timestamps. It could be done better, for
        # example checking the next version and calculate the middle time stamp
        # but regardless of what we do here, the result is erroneous, since it
        # will mess up the labeling.
        if ($timestamp < $last_timestamp) {
            $timestamp = $last_timestamp + 1;
            &ThrowWarning ("'$physname': wrong timestamp at version "
                           . "'$vernum'; setting timestamp to "
                           . "'$timestamp'");
        }
        $last_timestamp = $timestamp;

        $itemtype = $info->{type};
        $actiontype = $info->{action};

        if ($actiontype eq 'IGNORE') {
            next VERSION;
        }

        if ($itemtype == VSS_PROJECT
            && uc($physname) eq VSSDB_ROOT) {
            $itemname = &GetItemName($version->findvalue('Action/SSName'),
                                     $version->findvalue('Action/SSName/@offset'),
                                     $namelookup);
            if ($itemname eq '$/') {
                $itemname = '';
            }
            $tphysname = $version->findvalue('Action/Physical');
        } else {
            $itemname = &GetItemName($version->findvalue('Action/SSName'),
                                     $version->findvalue('Action/SSName/@offset'),
                                     $namelookup);
        }

        $comment = undef;
        $info = undef;
        $parentdata = 0;
        $label = undef;

        if ($version->exists('Comment')) {
            $comment = $version->findvalue('Comment') || undef;
        }

        # we can have label actions and labels attached to versions
        if ($version->exists('Action/Label')) {
            $label = $version->findvalue('Action/Label');
            my $lcom = $version->findvalue('Action/LabelComment');
            # append the label comment to a possible version comment
            if (defined $lcom && $lcom ne '') {
                if (defined $comment) {
                    say "Merging LabelComment and Comment for "
                        . "'$tphysname;$vernum'"; # if $gCfg{verbose};
                    $comment .= "\n";
                }
                $comment .= $lcom || undef;
            }
        }

        if (defined($comment)) {
            $comment =~ s/(?:\r\n|\r(?!\n))/\n/g;
            $comment =~ s/^\s+//s;
            $comment =~ s/\s+$//s;
        }

        if ($physname ne $tphysname) {
            # If version's physical name and file's physical name are different,
            # this is a project describing an action on a child item. Most of
            # the time, this very same data will be in the child's physical
            # file and with more detail (such as check-in comment).

            # However, in some cases (such as renames, or when the child's
            # physical file was later purged), this is the only place we'll
            # have the data; also, sometimes the child record doesn't even
            # have enough information about itself (such as which project it
            # was created in and which project(s) it's shared in).

            # So, for a parent record describing a child action, we'll set a
            # flag, then combine them in the next phase.

            $parentdata = 1;

            # OK, since we're describing an action in the child, the parent is
            # actually this (project) item

            $parentphys = $physname;
        }

        # set up priority and optionally info
        my @delete_actions = (ACTION_DELETE, ACTION_DESTROY);
        my @move_actions = (ACTION_MOVE_TO, ACTION_MOVE_FROM);
        for ($actiontype) {
            when (ACTION_ADD) {
                $priority = PA_PRIORITY_ADD;
            }
            when (ACTION_RENAME) {
                # if a rename, we store the new name in the action's 'info' field
                $info = &GetItemName($version->findvalue('Action/NewSSName'),
                                     $version->findvalue('Action/NewSSName/@offset'),
                                     $namelookup);
                $priority = PA_PRIORITY_NORMAL;
            }
            when (ACTION_BRANCH) {
                $info = $version->findvalue('Action/Parent');
                $priority = PA_PRIORITY_BRANCH;
            }
            when (@move_actions) {
                $info = $version->findvalue((($actiontype eq ACTION_MOVE_TO) ? 'Action/DestPath' : 'Action/SrcPath'));
                $info =~ s/^..(.*)$/$1/;
                $priority = PA_PRIORITY_NORMAL;
            }
            when (ACTION_SHARE) {
                # need these to reassemble SHARE+BRANCH actions
                $info = $version->findvalue('Action/Physical');
                $priority = PA_PRIORITY_SHARE;
            }
            when (ACTION_PIN) {
                $priority = PA_PRIORITY_PIN;
            }
            when (@delete_actions) {
                $priority = ($actiontype eq ACTION_DELETE) ? PA_PRIORITY_DELETE : PA_PRIORITY_DESTROY;
            }
            default {
                $priority = PA_PRIORITY_NORMAL;
            }
        }

        # These might fall under multiple actiontypes

        # since there is no corresponding client action for PIN, we need to
        # enter the concrete version number here manually
        # In a share action the pinnedToVersion attribute can also be set
        $vernum = $version->findvalue('Action/PinnedToVersion') if ($version->exists('Action/PinnedToVersion'));

        # for unpin actions also remeber the unpinned version
        $info = $version->findvalue('Action/UnpinnedFromVersion') if ($version->exists('Action/UnpinnedFromVersion'));

        # now everything is setup, add to database
        $pt_sth->execute($tphysname, $itemtype);
        $pa_sth->execute($tphysname, $vernum, $parentphys, $actiontype, $itemname,
                         $timestamp, $user, $info, $priority,
                         $parentdata, $comment);

        # attach label data
        my $linsert;
        if ($actiontype eq ACTION_LABEL) {
            $linsert = $gCfg{dbh}->last_insert_id("","","","");
            $li_sth->execute($linsert, $label // '');
        }

        # Handle version labels as a secondary action for the same version
        # version labels and label action use the same location to store the
        # label. Therefore it is not possible to assign a version label to
        # version where the actiontype was LABEL. But ssphys will report the
        # same label twice. Therefore filter the Labeling versions here.
        if ($version->exists('Label')
            && $actiontype ne ACTION_LABEL) {
            my ($labelComment);
            my $vlabel = $version->findvalue('Label');

            if ($version->exists('LabelComment')) {
                $labelComment = $version->findvalue('LabelComment');
            }
            else {
                $labelComment = "assigned label '$vlabel' to version $vernum of physical file '$tphysname'";
            }

            $pt_sth->execute($tphysname, $itemtype);
            $pa_sth->execute($tphysname, $vernum, $parentphys, ACTION_LABEL, $itemname,
                             $timestamp, $user, $info, PA_PRIORITY_NORMAL,
                             $parentdata, $labelComment);
            $linsert = $gCfg{dbh}->last_insert_id("","","","");
            $li_sth->execute($linsert, $vlabel // '');
        }
    }
}  #  End GetVssItemVersions

###############################################################################
#  GetItemName
###############################################################################
sub GetItemName {
    my($itemname, $offset, $namelookup) = @_;

    if (defined $offset
        && defined $namelookup->{$offset}
        && defined $namelookup->{$offset}->{name}) {
        my $newname = $namelookup->{$offset}->{name};
        say "Changing name of '$itemname' to '$newname' from "
            . "name cache" if $gCfg{debug};
        $itemname = $newname;
    }

    return $itemname;
}  #  End GetItemName

###############################################################################
#  TestGitAuthorInfo
###############################################################################
sub TestGitAuthorInfo {
    # Now that we have the physical history, test our author data
    my($sth, $tth, $rows);
    my @amk = keys %{$author_map}; # grab all the usernames
    my $in_clause = join q{,}, ('?') x (scalar @amk);
    my $err = 0;

    $gCfg{resume} = 0;

    $sth = $gCfg{dbh}->prepare("SELECT DISTINCT author "
                               ."FROM PhysicalAction "
                               . "WHERE author NOT IN ($in_clause) "
                               . "ORDER BY author");
    $sth->execute(@amk);
    $rows = $sth->fetchall_arrayref( {} );

    foreach my $row (@$rows) {
        ++$err;
        say "Found unknown username `$row->{author}'.";
    }

    die "author file '$gCfg{author_info}' is incomplete." if $err;

    1;
}

###############################################################################
#  GitReadImage
###############################################################################
sub GitReadImage {
    # Read the physical actions, and perform them on the repository

    my $repo = Git::Repository->new(work_tree => "$gCfg{repo}");
    $repo->setlog($gCfg{debug});

    # phys_ac_count is only the maximum
    my ($phys_ac_count) = $gCfg{dbh}->selectrow_array('SELECT COUNT(*) FROM PhysicalAction');
    my $progress;
    my $next_update;

    if (!($gCfg{debug} || $gCfg{verbose})) {
        $progress = Term::ProgressBar->new({name  => 'Actions',
                                            count => $phys_ac_count,
                                            ETA   => 'linear', });
        $progress->max_update_rate(1);
    }


    my $head_id;
    my $last_time;
    my $sth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalActionSchedule ORDER BY schedule_id');
    my $tth = $gCfg{dbh}->prepare('SELECT MIN(timestamp) FROM PhysicalAction WHERE timestamp > ?');

    my $it_sth = $gCfg{dbh}->prepare('SELECT itemtype FROM PhysItemtype WHERE physname = ?');
    my $cp_sth = $gCfg{dbh}->prepare('UPDATE SystemInfo SET gri_timestamp = ?, gri_git_head = ?, gri_next_update = ?, '
                                     . 'gri_git_image = ?, gri_destroyed_files = ?, gri_exclude = ?');
    my $d_sth = $gCfg{dbh}->prepare('DELETE FROM PhysicalActionSchedule');
    my $r_sth = $gCfg{dbh}->prepare('INSERT INTO PhysicalActionRetired '
                                    . 'SELECT NULL AS retired_id, '
                                    . '? AS commit_id, * FROM PhysicalActionSchedule '
                                    . 'ORDER BY schedule_id');

    if ($gCfg{resume}) {
        $last_time = $gCfg{gri_timestamp};
        $head_id = $gCfg{gri_git_head};
        $next_update = $gCfg{gri_next_update};
        %git_image = %{ thaw($gCfg{gri_git_image}) };
        $destroyed_files = thaw($gCfg{gri_destroyed_files});
        open my $fh, '>', $gCfg{exclude} or die "error writing $gCfg{exclude}: $!";
        print $fh $gCfg{gri_exclude};
        close $fh;
        $repo->logrun('reset' => '--hard', $head_id);
        # now we need to verify that all hard links are valid
        # we assume that if there's a difference, what is in
        # git is what should be in the link file, and hard link again
        foreach my $dbe (keys %git_image) {
            if (ref($git_image{$dbe})) {
                my $link_file = File::Spec->catfile($gCfg{links}, $dbe);
                my ($link_ino, $path_ino);
                my @path_inos;

                (undef, $link_ino) = stat($link_file);
                my @lf_inos =  ($link_ino) x (scalar @{$git_image{$dbe}});

                foreach my $path (@{$git_image{$dbe}}) {
                    (undef, $path_ino) = stat($path);
                    push @path_inos, $path_ino;
                }
                if (!(@lf_inos ~~ @path_inos)) {
                    if (!copy($git_image{$dbe}[0], $link_file)) {
                        warn "GitReadImage: resume path: `$git_image{$dbe}[0]', link `$link_file' copy $!";
                    }
                    foreach my $path (@{$git_image{$dbe}}) {
                        unlink $path;
                        link $link_file, $path; # add $path as the new link
                    }
                }
            }
        }
        $gCfg{resume} = 0;
    } else {
        my $username;
        ($username, $last_time) = $gCfg{dbh}->selectrow_array('SELECT author, timestamp '
                                                              . 'FROM PhysicalAction '
                                                              . 'WHERE timestamp = '
                                                              . '(SELECT MIN(timestamp) FROM PhysicalAction)');
        my $map = $author_map->{$username};

        # Insert an empty commit
        $repo->logrun( commit => '--allow-empty', '--no-edit', '-m', 'Initial commit',
                       {
                           env => {
                               GIT_AUTHOR_NAME => $map->{name},
                               GIT_AUTHOR_EMAIL => $map->{email},
                               GIT_AUTHOR_DATE => POSIX::strftime(ISO8601_FMT, localtime($last_time)),
                               GIT_COMMITTER_DATE => POSIX::strftime(ISO8601_FMT, localtime($last_time)),
                           }
                       });

        $head_id = $repo->logrun('rev-parse' => 'HEAD');
        $next_update = 0;

        # checkpoint now
        my $giti = nfreeze \%git_image;
        my $df = nfreeze $destroyed_files;

        open my $fh, '<', $gCfg{exclude} or die "error opening $gCfg{exclude}: $!";
        my $data = do { local $/; <$fh> };
        close $fh;

        $cp_sth->execute($last_time, $head_id, $next_update, $giti, $df, $data);
    }

    my $dump_cnt = $next_update;
    while ($last_time < $gCfg{maxtime}) {
        my ($username, $comment);

        say "timestamp: $last_time" if $gCfg{verbose};

        $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
        eval {
            &SchedulePhysicalActions($last_time);

            $sth->execute();
            my $rows = $sth->fetchall_arrayref( {} );

            undef $username;

            # It's not an error to have 0 scheduled rows

            foreach my $row (@$rows) {
                $last_time = $row->{timestamp};
                $username = $row->{author};
                $comment = $row->{comment};

                my ($path, $parentpath);

#            if ($dump_cnt % 100 == 0) {
#                say "git_image: " . Dumper(\%git_image) if $gCfg{debug};
#                say "destroyed files: " . Dumper($destroyed_files) if $gCfg{debug};
#                if ($dump_cnt == 100) {
#                    exit(0);
#                }
#            }
                ++$dump_cnt;

                $it_sth->execute($row->{physname});
                ($row->{itemtype}) = $it_sth->fetchrow_array();

                if (defined $row->{parentphys}) {
                    say "parentphys: $row->{parentphys} "
                        . "physname: $row->{physname} "
                        . "timestamp: $row->{timestamp}" if $gCfg{debug};
                    $parentpath = $git_image{$row->{parentphys}};
                    $path = ($row->{itemtype} == VSS_PROJECT)
                        ? File::Spec->catdir($parentpath, $row->{itemname})
                        : File::Spec->catfile($parentpath, $row->{itemname});
                } else {
                    # presumably this is a child entry
                    # pick a path to update
                    if (defined $row->{physname}
                        && defined $git_image{$row->{physname}}) {
                        $path = @{$git_image{$row->{physname}}}[0];
                        $parentpath = dirname($path);
                    }
                }

                &UpdateGitRepository($row, $parentpath, $path, \%git_image, $repo);
            }

            if (defined $username) {
                &GitCommit($repo, $comment, $username, $last_time);
                ++$gCfg{commit_id};
                $head_id = $repo->logrun('rev-parse' => 'HEAD');

                # write the checkpoint
                my $giti = nfreeze \%git_image;
                my $df = nfreeze $destroyed_files;

                open my $fh, '<', $gCfg{exclude} or die "error opening $gCfg{exclude}: $!";
                my $data = do { local $/; <$fh> };
                close $fh;

                $cp_sth->execute($last_time, $head_id, $next_update, $giti, $df, $data);
            }

            # get the next changeset
            if ($last_time < $gCfg{maxtime}) {
                $tth->execute($last_time);
                $last_time = $tth->fetchall_arrayref()->[0][0];
            }

            # Retire old data
            $r_sth->execute($gCfg{commit_id});
            $d_sth->execute();
        };
        if ($@) {
            warn "Transaction aborted because $@";
            eval { $gCfg{dbh}->rollback };
            die "Failed to commit changeset";
        } else {
            $gCfg{dbh}->commit;
        }

        if (defined $progress) {
            $next_update = $progress->update($dump_cnt)
                if $dump_cnt > $next_update || $dump_cnt == $phys_ac_count;
        }
    }

    # document our hard links for 'git pull'
    # Found this at a response to a question on how to handle hard links with git
    # at Stack Overflow <http://stackoverflow.com/questions/3729278/git-and-hard-links>.
    # The response given by Niloct <http://stackoverflow.com/users/152016/niloct>
    # here <http://stackoverflow.com/a/9322283/425738> is what I based this code on.
    # Neither Stack Overflow nor Niloct endorses me or my use of their work.
    # SO is CC BY-SA 3.0 <http://creativecommons.org/licenses/by-sa/3.0/>
    # at the time of this writing.
    my @shares = ();
    my @appdir = ('$GIT_DIR', File::Spec->updir());
    foreach my $key (keys %git_image) {
        if (ref($git_image{$key})) {
            my $ary = $git_image{$key};
            my $base = shift @$ary;
            $base =~ s/$repo_re//;

            if (scalar @$ary > 0) {
                my @basedir = File::Spec->splitdir($base);
                @basedir = (@appdir, @basedir);

                my $basepath = File::Spec->catfile(@basedir);

                push @shares, "#", "# $base", "#";

                # synthesize the hard link
                # XXX This could be a shell quoting nightmare...
                foreach my $e (@$ary) {
                    $e =~ s/$repo_re//;
                    my @edir = File::Spec->splitdir($e);
                    @edir = (@appdir, @edir);

                    my $linkpath = File::Spec->catfile(@edir);
                    my $link = 'ln -f "' . $basepath . '"  "' . $linkpath . '"';
                    push @shares, $link;
                }
            }
        }
    }

    if (scalar @shares > 0) {
        my $file = File::Spec->catfile($gCfg{repo}, '.git', 'hooks', 'post-merge');
        open FILE, ">$file";
        print FILE <<"EOT";
#!/bin/sh
#
# This collection of files remained shared at the end of VSS conversion.
# git does not natively deal with shares, so this file may be deleted.
# However, the links must be snapped, which may be accomplished by checking
# out a clean copy from this repository.
#
EOT
        foreach my $s (@shares) {
            print FILE "$s\n";
        }
        close FILE;
        chmod 0755, $file;
    }

    # don't know if phys_ac_count was actually reached in the loop
    if (defined $progress) {
        $next_update = $progress->update($phys_ac_count)
            if $phys_ac_count >= $next_update;
    }

    1;
}

###############################################################################
#  ReplayLabels
###############################################################################
sub ReplayLabels {
    # Read the labels, checking out the particular bookmark for a label.
    my $repo = Git::Repository->new(work_tree => "$gCfg{repo}");
    $repo->setlog($gCfg{debug});

    my ($label_count) = $gCfg{dbh}->selectrow_array('SELECT COUNT(*) FROM LabelBookmark');
    my $prg_count;
    my $progress;
    my $next_update = 0;

    if (!($gCfg{debug} || $gCfg{verbose})) {
        $progress = Term::ProgressBar->new({name  => 'Labels',
                                            count => $label_count,
                                            ETA   => 'linear', });
        $progress->max_update_rate(1);
    }

    my $cp_sth = $gCfg{dbh}->prepare('UPDATE SystemInfo SET rl_next_update = ?, rl_label_map = ?');
    if ($gCfg{resume}) {
        $next_update = $gCfg{rl_next_update};
        $label_map = thaw($gCfg{rl_label_map});
        tie %{$label_map}, 'Hash::Case::Preserve';
        $repo->logrun('reset' => '--hard');
        $gCfg{resume} = 0;
    } else {
        my $lm = nfreeze $label_map;
        $cp_sth->execute($next_update, $lm);
    }


    $gCfg{dbh}->do('DELETE FROM PhysicalActionSchedule'); # for resume
    $gCfg{dbh}->do('DELETE FROM PhysicalActionChangeset');
    $gCfg{dbh}->do("INSERT INTO PhysicalActionSchedule "
                   ."SELECT * "
                   ."FROM PhysicalActionLabel "
                   ."WHERE action_id NOT IN "
                   ."(SELECT action_id FROM PhysicalActionRetired WHERE actiontype = '@{[ACTION_LABEL]}') "
                   ."ORDER BY schedule_id");

    my $last_time = &ResetTimestampFromSchedule();

    my $sth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalActionSchedule ORDER BY schedule_id');

    my $tth = $gCfg{dbh}->prepare("SELECT MIN(timestamp) "
                                  . "FROM PhysicalAction "
                                  . "WHERE timestamp > ? "
                                  . "AND actiontype = '@{[ACTION_LABEL]}'");
    my $uth = $gCfg{dbh}->prepare('SELECT head_id, git_image FROM LabelBookmark WHERE schedule_id = ?');
    my $it_sth = $gCfg{dbh}->prepare('SELECT itemtype FROM PhysItemtype WHERE physname = ?');
    my $l_sth = $gCfg{dbh}->prepare('SELECT label FROM PhysLabel WHERE action_id = ?');
    my $d_sth = $gCfg{dbh}->prepare('DELETE FROM PhysicalActionSchedule');
    my $r_sth = $gCfg{dbh}->prepare('INSERT INTO PhysicalActionRetired '
                                    . 'SELECT NULL AS retired_id, '
                                    . '? AS commit_id, * FROM PhysicalActionSchedule '
                                    . 'ORDER BY schedule_id');

    my $first_label = 0;
    my $dump_cnt;
    while (defined $last_time && $last_time < $gCfg{maxtime}) {
        my ($username, $comment);

        say "timestamp label: $last_time" if $gCfg{verbose};

        $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
        eval {
            if ($first_label != 0) {
                # These have been scheduled already, no need to go through
                # that code again, just get a changeset
                &InsertPhysicalActionChangeset();
            }

            $last_time = &ResetTimestampFromSchedule();

            &GetOneChangeset($last_time);

            $sth->execute();
            my $rows = $sth->fetchall_arrayref( {} );

            undef $username;

            # It's not an error to have 0 scheduled rows

            $dump_cnt = 0;
            foreach my $row (@$rows) {
                $last_time = $row->{timestamp};
                $username = $row->{author};
                $comment = $row->{comment};

                my ($path, $parentpath);

                if ($dump_cnt == 0) {
                    $l_sth->execute($row->{action_id});
                    ($row->{label}) = $l_sth->fetchrow_array();

                    my $tagname = get_valid_ref_name($row->{label}, $row->{timestamp});

                    if (!defined $row->{label} || !defined $label_map->{$row->{label}}) {
                        # create a new branch for this label
                        # invalid labels are not recorded in label map
                        $repo->logrun(checkout => '-q', '--orphan',  $tagname);
                        if (defined $row->{comment} && $row->{comment} ne '') {
                            $repo->logrun(config => "branch." . $tagname . ".description",  $row->{comment}); # give it a description
                        }
                        $repo->logrun(reset => '--hard'); # unmark all the "new" files from the commit.
                        if (!invalid_branch_name($row->{label})) {
                            $label_map->{$row->{label}} = $tagname;
                            say "Label `$row->{label}' is branch `$tagname'.";
                        } else {
                            say "undef label is branch `$tagname' at timestamp $row->{timestamp}.";
                        }
                    } else {
                        $repo->logrun(checkout => '-q', $tagname);
                    }
                }

                ++$dump_cnt;

                $uth->execute($row->{schedule_id});

                my ($head_id, $giti) = $uth->fetchrow_array();
                $giti = thaw($giti);

                $it_sth->execute($row->{physname});
                ($row->{itemtype}) = $it_sth->fetchrow_array();

                if (defined $row->{parentphys}) {
                    say "label parentphys: $row->{parentphys} "
                        . "physname: $row->{physname} "
                        . "timestamp: $row->{timestamp}" if $gCfg{debug};
                    $parentpath = $giti->{$row->{parentphys}};
                    $path = ($row->{itemtype} == VSS_PROJECT)
                        ? File::Spec->catdir($parentpath, $row->{itemname})
                        : File::Spec->catfile($parentpath, $row->{itemname});
                    # wrap path in array
                    my @p = ("$path");
                    $path = \@p;
                } else {
                    # presumably this is a child entry
                    # pick a path to update
                    if (defined $row->{physname}
                        && defined $giti->{$row->{physname}}) {
                        # no such thing as a unique "path" with shares
                        $path = $giti->{$row->{physname}};
                    }
                }

                &GitLabel($row, $repo, $head_id, $path);
            }

            if (defined $username) {
                &GitCommit($repo, $comment, $username, $last_time);
                ++$gCfg{commit_id};

                my $lm = nfreeze $label_map;
                $cp_sth->execute($next_update, $lm);
            }

            # get the next changeset
            if ($last_time < $gCfg{maxtime}) {
                $tth->execute($last_time);
                $last_time = $tth->fetchall_arrayref()->[0][0];
            }

            # Retire old data
            $r_sth->execute($gCfg{commit_id});
            $d_sth->execute();
            ++$first_label;
        };
        if ($@) {
            warn "Transaction aborted because $@";
            eval { $gCfg{dbh}->rollback };
            die "Failed to commit label";
        } else {
            $gCfg{dbh}->commit;
        }

        if (defined $progress) {
            $prg_count += $dump_cnt;
            $next_update = $progress->update($prg_count)
                if $prg_count > $next_update || $prg_count == $label_count;
        }
    }


    1;
}

###############################################################################
#  Cleanup
###############################################################################
sub Cleanup {
    # cleanup files
    $gCfg{resume} = 0;

    # snap the links
    rmtree($gCfg{links});

    # delete deleted files
    rmtree($gCfg{deleted});

    # checkout git master so we are in a nice state
    my $repo = Git::Repository->new(work_tree => "$gCfg{repo}");
    $repo->setlog($gCfg{debug});

    $repo->logrun(checkout => 'master');

    1;
}

###############################################################################
# RemoveTemporaryCheckIns
# remove temporary checkins that where create to detect MS VSS capabilities
###############################################################################
sub RemoveTemporaryCheckIns {

    $gCfg{resume} = 0;

    # more info at "Elimination of ~SAK Files" : <http://msdn.microsoft.com/en-us/library/bb165458(v=vs.80).aspx>
    my $sql = <<"EOSQL";
DELETE FROM PhysicalAction WHERE action_id IN
(SELECT action_id
 FROM PhysicalAction
 WHERE physname IN
 (SELECT A.physname AS physname
  FROM PhysicalAction AS A, PhysItemtype AS B
  WHERE A.physname = B.physname
  AND A.actiontype = '@{[ACTION_ADD]}'
  AND B.itemtype = @{[VSS_FILE]}
  AND A.itemname LIKE '~sak%'
  AND A.comment LIKE 'Temporary file created by Visual Studio%'))
EOSQL

    $gCfg{dbh}->do($sql);

    1;
}

###############################################################################
# FixupParentActions
# Fixes up typical ACTION_ADD, ACTION_BRANCH/ACTION_SHARE
# missing comment data for parents in PhysicalAction
###############################################################################
sub FixupParentActions {

    $gCfg{resume} = 0;

    $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
    eval {
        # Fill in comment data for parents.  This makes it easier
        # to group them into changesets.  There's probably a better
        # way of doing this, but this is easy.
        my $sql = <<"EOSQL";
SELECT B.comment AS comment, A.action_id AS action_id
FROM (SELECT X.physname AS physname, X.action_id AS action_id
      FROM PhysicalAction AS X, PhysItemtype AS Y
      WHERE X.physname = Y.physname
      AND Y.itemtype = ?
      AND X.parentdata != 0
      AND X.actiontype = '@{[ACTION_ADD]}') AS A
NATURAL JOIN (SELECT X.physname AS physname, X.comment AS comment
              FROM PhysicalAction AS X, PhysItemtype AS Y
              WHERE X.physname = Y.physname
              AND Y.itemtype = ?
              AND X.parentdata = 0
              AND X.actiontype = '@{[ACTION_ADD]}') AS B
EOSQL

        my $sth = $gCfg{dbh}->prepare($sql);
        my $tth = $gCfg{dbh}->prepare('UPDATE PhysicalAction '
                                      .'SET comment = ? '
                                      .'WHERE action_id = ? '
                                      .'AND comment IS NULL ');
        my $row;

        foreach my $type (VSS_PROJECT, VSS_FILE) {
            $sth->execute($type, $type);

            while (defined($row = $sth->fetchrow_hashref() )) {
                $tth->execute($row->{comment}, $row->{action_id});
            }
        }

        # timestamp seems to be earlier in child than parent
        # give each SHARE/BRANCH a little wiggle room timestamp-wise
        $sql = <<"EOSQL";
SELECT B.comment AS comment, A.action_id AS action_id
FROM (SELECT X.info AS info, X.action_id AS action_id, X.timestamp AS timestamp
      FROM PhysicalAction AS X, PhysItemtype AS Y
      WHERE X.physname = Y.physname
      AND Y.itemtype = @{[VSS_FILE]}
      AND X.parentdata != 0
      AND X.actiontype IN ('@{[ACTION_BRANCH]}', '@{[ACTION_SHARE]}')) AS A
INNER JOIN (SELECT X.info AS info, X.comment AS comment, X.timestamp AS timestamp
              FROM PhysicalAction AS X, PhysItemtype AS Y
              WHERE X.physname = Y.physname
              AND Y.itemtype = @{[VSS_FILE]}
              AND X.parentdata = 0
              AND X.actiontype = '@{[ACTION_BRANCH]}') AS B
ON A.info = B.info AND A.timestamp BETWEEN B.timestamp-@{[TIMESTAMP_DELTA]} AND B.timestamp+@{[TIMESTAMP_DELTA]}
EOSQL

        $sth = $gCfg{dbh}->prepare($sql);
        $tth = $gCfg{dbh}->prepare('UPDATE PhysicalAction '
                                   . 'SET comment = ? '
                                   . 'WHERE action_id = ? '
                                   . "AND comment IS NULL");
        $sth->execute();

        while (defined($row = $sth->fetchrow_hashref() )) {
            $tth->execute($row->{comment}, $row->{action_id});
        }

        # When a VSS_PROJECT is moved, it duplicates the ADD from the
        # project that contained the moved project before the move.
        # This is bad for our move implementation,
        # so scrap these non-parentdata ADD records.
        $sql = <<"EOSQL";
DELETE FROM PhysicalAction
WHERE action_id IN
(SELECT C.action_id AS action_id
FROM (SELECT X.physname AS physname, X.parentphys AS parentphys
      FROM PhysicalAction AS X, PhysItemtype AS Y
      WHERE X.physname = Y.physname
      AND X.actiontype = '@{[ACTION_ADD]}'
      AND X.parentdata != 0
      AND Y.itemtype = @{[VSS_PROJECT]}) AS A
INNER JOIN (SELECT X.physname AS physname, X.parentphys AS parentphys
            FROM PhysicalAction AS X, PhysItemtype AS Y
            WHERE X.physname = Y.physname
            AND X.actiontype = '@{[ACTION_MOVE_TO]}'
            AND X.parentdata != 0
            AND Y.itemtype = @{[VSS_PROJECT]}) AS B
USING (physname, parentphys)
INNER JOIN (SELECT X.action_id AS action_id, X.physname AS physname
      FROM PhysicalAction AS X, PhysItemtype AS Y
      WHERE X.physname = Y.physname
      AND X.actiontype = '@{[ACTION_ADD]}'
      AND X.parentdata = 0
      AND Y.itemtype = @{[VSS_PROJECT]}) AS C
USING (physname))
EOSQL

        $gCfg{dbh}->do($sql);
    };

    if ($@) {
        warn "Transaction aborted because $@";
    eval { $gCfg{dbh}->rollback };
        die "Failed to fix up parents";
    } else {
        &SetSystemTask( $gCfg{next_task}->{task} );
        $gCfg{dbh}->commit;
    }

    1;
}

###############################################################################
#  CheckForDestroy
###############################################################################
sub CheckForDestroy {
    my($exportdir, $physname, $version, $destroyonly, $is_destroyed) = @_;
    my($row, $physpath, $rowd);
    my $tmp_sth;

    $$is_destroyed = 0;

    # physical file doesn't exist; it must have been destroyed earlier
    # search and see if it was DESTROYed first
    $tmp_sth = $gCfg{dbh}->prepare_cached("SELECT action_id FROM PhysicalAction "
                                          . "WHERE physname = ? AND "
                                          . "actiontype = '@{[ACTION_DESTROY]}'",
                                          { dbi_dummy => __FILE__.__LINE__ });
    $tmp_sth->execute($physname);
    ($row) = $tmp_sth->fetchrow_array();
    $tmp_sth->finish();

    if (!$destroyonly) {
        $tmp_sth = $gCfg{dbh}->prepare_cached("SELECT action_id FROM PhysicalAction "
                                              . "WHERE physname = ? AND "
                                              . "actiontype = '@{[ACTION_DELETE]}'",
                                              { dbi_dummy => __FILE__.__LINE__ });
        $tmp_sth->execute($physname);
        ($rowd) = $tmp_sth->fetchrow_array();
        $tmp_sth->finish();
    }

    my $ftc = $row // $rowd;
    $ftc = (defined $ftc) ? (($$is_destroyed = ($ftc == $row)) ? $gCfg{destroyedFile} : $gCfg{deletedFile} ) : $gCfg{indeterminateFile};

    if ($ftc eq $gCfg{indeterminateFile}) {
        # we have no idea if it was DESTROYed or DELETEd
        &ThrowWarning("Can't retrieve revisions from physical file "
                      . "'$physname'; it was possibly corrupted or was not in place before "
                      . "the last GETPHYSHIST task was run.");
    }
    $physpath = File::Spec->catfile($exportdir, "$physname.$version");
    if (! -e $physpath) {
        if (!copy($ftc, $physpath)) {
            warn "CheckForDestroy: file: `$ftc', copy $!";
        }
    }
    return $physpath;
}

###############################################################################
#  ExportVssPhysFile
###############################################################################
sub ExportVssPhysFile {
    my($physname, $version, $is_destroyed) = @_;
    my($row, $physpath);
    my $tmp_sth;

    $physname =~ m/^(..)/;
    $version = $version // 1;

    my $exportdir = File::Spec->catdir($gCfg{vssdata}, $1);

    make_path($exportdir) if ! -e $exportdir;
    $tmp_sth = $gCfg{dbh}->prepare_cached('SELECT datapath FROM Physical WHERE physname = ?',
                                          { dbi_dummy => __FILE__.__LINE__ });
    $tmp_sth->execute($physname);
    ($row) = $tmp_sth->fetchrow_array();
    $tmp_sth->finish();

    $physpath = $row // &CheckForDestroy($exportdir, $physname, $version, 1, $is_destroyed);

    if (! -f $physpath) {
        # physical file doesn't exist; it must have been destroyed later since find was run
        &ThrowWarning("Can't retrieve revisions from VSS database file "
                      . "'$physpath'; it was destroyed after the last GETPHYSHIST task was run.");
        return undef;
    }

    my $exportfile = File::Spec->catfile($exportdir, "$physname.$version");

    if (! -e $exportfile) {
        # get all versions we can find from the physical file
        my @cmd = ('get', '-b', "-v$version", '--force-overwrite',
                   "-e$gCfg{encoding}", $physpath,
                   File::Spec->catdir($exportdir, $physname));
        &DoSsCmd(@cmd);
        if (! -e $exportfile) {
            $physpath = &CheckForDestroy($exportdir, $physname, $version, 0, $is_destroyed);
        }
    }

    return $exportfile;
}  #  End ExportVssPhysFile

###############################################################################
#  ShowHeader
###############################################################################
sub ShowHeader {
    my $info = $gCfg{task} eq TASK_INIT ? 'BEGINNING CONVERSION...' :
        "RESUMING CONVERSION FROM TASK '$gCfg{task}'...";
    my $starttime = ctime($^T);

    my $ssversion = &GetSsVersion();

    print <<"EOTXT";
======== @{[PROGNAME]} ========
$info
Start Time   : $starttime

VSS Dir      : $gCfg{vssdir}
Temp Dir     : $gCfg{tempdir}
git repo     : $gCfg{repo}
VSS Encoding : $gCfg{encoding}

@{[PROGNAME]} ver  : $VERSION
@{[SSPHYS]} exe   : $gCfg{ssphys}
@{[SSPHYS]} ver   : $ssversion
Task         : $gCfg{task}
Rev Time     : $gCfg{revtimerange}

EOTXT

    my @version = split '\.', $ssversion;
    # we need at least ssphys 0.22
    if ($version[0] == 0 && $version[1] < 22) {
        &ThrowError("The conversion needs at least @{[SSPHYS]} version 0.22");
    }

}  #  End ShowHeader

###############################################################################
#  ShowSummary
###############################################################################
sub ShowSummary {

    if (keys(%gErr) || $gCfg{resume}) {
       print <<"EOTXT";
=============================================================================
                               ERROR SUMMARY

EOTXT

        if($gCfg{resume}) {
            print <<"EOTXT";
**NOTICE** Because this run was resumed from a previous run, this may be only
a partial list; other errors may have been reported during previous run.

EOTXT
        }

        foreach my $task (@{ $gCfg{errortasks} }) {
            print "\n$task:\n   ";
            print join("\n   ", @{ $gErr{$task} }),"\n";
        }
    }

    print <<"EOTXT";
=============================================================================
                             END OF CONVERSION

The VSS to GIT conversion is complete.

If any errors occurred during the conversion, they are summarized above.

For more information on the @{[PROGNAME]} project, see:
@{[PROGNAME_URL]}

EOTXT

    my $starttime = ctime($^T);
    chomp $starttime;
    my $endtime = ctime(time);
    chomp $endtime;
    my $elapsed;

    {
        use integer;
        my $secs = time - $^T;
        my @fmt;
        my @fmt_data;
        my @time_params = (
            {'d' => (3600*24)},
            {'h' => 3600},
            {'m' => 60}
            );

        my $first_time = 1;
        foreach my $t (@time_params) {
            my ($dur_name, $dur_time) = each %$t;

            if ((!$first_time && (scalar @fmt_data) > 0) || $secs >= $dur_time) {
                my $dur = $secs / $dur_time;
                $secs %= $dur_time;
                push @fmt, "%2.2i$dur_name";
                push @fmt_data, $dur;
            }
            $first_time = 0;
        }

        push @fmt, "%2.2is";
        push @fmt_data, $secs;

        $elapsed = sprintf(join(" ", @fmt), @fmt_data);
    }

    my($actions, $revisions, $mintime, $maxtime) = &GetStats();

    print <<"EOTXT";
Started at              : $starttime
Ended at                : $endtime
Elapsed time            : $elapsed

VSS Actions read        : $actions
git commits converted   : $revisions
Date range (YYYY-MM-DD) : $mintime to $maxtime

EOTXT

}  #  End ShowSummary

###############################################################################
#  GetStats
###############################################################################
sub GetStats {
    my($actions, $mintime, $maxtime);

    ($actions) = $gCfg{dbh}->selectrow_array('SELECT COUNT(*) FROM PhysicalActionRetired');

    $mintime = $gCfg{mintime};
    $maxtime = $gCfg{maxtime};

    foreach($mintime, $maxtime) {
        $_ = POSIX::strftime(MINMAX_TIME_FMT, localtime($_));
    }

    return($actions, $gCfg{commit_id}-1, $mintime, $maxtime);

}  #  End GetStats

###############################################################################
#  DoSsCmd
###############################################################################
sub DoSsCmd {
    my(@cmd) = @_;

    my $ok = &DoSysCmd(@cmd);

    $gSysOut =~ s/\x00//g; # remove null bytes
    $gSysOut =~ s/.\x08//g; # yes, I've seen VSS store backspaces in names!
}  #  End DoSsCmd

###############################################################################
#  DoSysCmd
###############################################################################
sub DoSysCmd {
    my(@args) = @_;
    my $allowfail = 1;

    unshift @args, $gCfg{ssphys};

    say join(" ", @args) if $gCfg{verbose};

    run \@args, '>', \$gSysOut;

    print $gSysOut if $gCfg{debug};

    my $rv = 1;

    if ($? == -1) {
        &ThrowWarning("FAILED to execute: $!");
        die unless $allowfail;

        $rv = 0;
    } elsif ($?) {
        &ThrowWarning(sprintf "FAILED with non-zero exit status %d (cmd: `%s')", $? >> 8, join(" ", @args));
        die unless $allowfail;

        $rv = 0;
    }

    return $rv;

}  #  End DoSysCmd

###############################################################################
#  GetSsVersion
###############################################################################
sub GetSsVersion {
    my(@args) = ($gCfg{ssphys}, '--version');
    my $out;

    run \@args, '>&', \$out;
    # Build numbers look like:
    #  a.) ssphys 0.20.0, Build 123
    #  b.) ssphys 0.20.0, Build 123:150
    #  c.) ssphys 0.20.0, Build 123:150 (locally modified)
    $out =~ m/^ssphys (.*?), Build (.*?)[ \n]/m;

    # turn it into
    #  a.) 0.20.0.123
    #  b.) 0.20.0.123:150
    #  c.) 0.20.0.123:150
    return $1 . "." . $2 || 'unknown';
}  #  End GetSsVersion

###############################################################################
#  ThrowWarning
###############################################################################
sub ThrowWarning {
    my($msg, $callinfo) = @_;

    $callinfo ||= [caller()];

    $msg .= "\nat $callinfo->[1] line $callinfo->[2]";

    warn "ERROR -- $msg\n";

    my $task = $gCfg{task};

    if(!defined $gErr{$task}) {
        $gErr{$task} = [];
        push @{ $gCfg{errortasks} }, $task;
    }

    push @{ $gErr{$task} }, $msg;

}  #  End ThrowWarning

###############################################################################
#  ThrowError
###############################################################################
sub ThrowError {
    &ThrowWarning(@_, [caller()]);
    &StopConversion;
}  #  End ThrowError

###############################################################################
#  StopConversion
###############################################################################
sub StopConversion {
    &DisconnectDatabase;

    exit(1);
}  #  End StopConversion

###############################################################################
#  SetSystemTask
###############################################################################
sub SetSystemTask {
    my($task) = @_;

    $gCfg{dbh}->do('UPDATE SystemInfo SET task = ?', undef, $task);
    $gCfg{task} = $task;

}  #  End SetSystemTask

###############################################################################
#  ConnectDatabase
###############################################################################
sub ConnectDatabase {
    my $db = $gCfg{sqlitedb};

    if (-e $db && (!$gCfg{resume} ||
                   ($gCfg{task} eq TASK_INIT))) {

        unlink $db or &ThrowError("Could not delete existing database "
                                  .$gCfg{sqlitedb});
    }

    print "Connecting to database $db\n\n";

    $gCfg{dbh} = DBI->connect("dbi:SQLite:dbname=$db", '', '',
                              {RaiseError => 1, AutoCommit => 1})
        or die "Couldn't connect database $db: $DBI::errstr";

    $gCfg{dbh}->func( 'vss_phys_to_num', 1, \&PhyToNum, 'create_function' );

}  #  End ConnectDatabase

###############################################################################
#  DisconnectDatabase
###############################################################################
sub DisconnectDatabase {
    $gCfg{dbh}->disconnect if defined $gCfg{dbh};
}  #  End DisconnectDatabase

###############################################################################
#  SetupGlobals
###############################################################################
sub SetupGlobals {
    if (!$gCfg{resume}) {
        &InitSysTables;
    } else {
        &ReloadSysTables;
    }
}  #  End SetupGlobals

###############################################################################
#  InitSysTables
###############################################################################
sub InitSysTables {
    my($sql);

    # The Physical table tracks the VSS database units (physname)
    # and where they are on the filesystem (datapath)
    $sql = <<"EOSQL";
CREATE TABLE
    Physical (
        physname    VARCHAR NOT NULL PRIMARY KEY,
        datapath    VARCHAR
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # NameLookup contains VSS name mappings for better filenames
    $sql = <<"EOSQL";
CREATE TABLE
    NameLookup (
        offset      INTEGER PRIMARY KEY,
        name        VARCHAR
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # FileBinary contains VSS is_binary types for VSS_FILES
    $sql = <<"EOSQL";
CREATE TABLE
    FileBinary (
        physname  VARCHAR NOT NULL PRIMARY KEY,
        is_binary INTEGER
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # PhysItemtype contains VSS itemtypes (VSS_PROJECT, VSS_FILE)
    $sql = <<"EOSQL";
CREATE TABLE
    PhysItemtype (
        physname  VARCHAR NOT NULL PRIMARY KEY,
        itemtype INTEGER
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # The PhysicalAction table is the raw output of the entire
    # VSS database with a few fixups.  It's basically a collection
    # of the actions that happened to all files and projects.
    # There's also some scheduling info (priority, parentdata)
    # that is emitted as this table is constructed.
    my @pa_ary;
    foreach my $param (@physical_action_params) {
        my($field, $type);
        while (($field, $type) = each %$param) {
            push @pa_ary, "$field $type";
        }
    }
    my $pa_sql = join(', ', @pa_ary);

    $sql = <<"EOSQL";
CREATE TABLE
    PhysicalAction (
        action_id   INTEGER PRIMARY KEY,
        $pa_sql
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # The PhysicalActionSchedule table starts out as a timeslice of
    # ($gCfg{revtimerange} s) the PhysicalAction table.  There's
    # basically two things that happen when data is in here:
    # -- The exact ordering of operations in the timeslice is fixed,
    #    (e.g. directories exist when files are added to them) since
    #    the ordering from the VSS database isn't exact enough.
    # -- Exactly one git changeset is synthesized from this ordering.
    #    Any additional changesets are stored in PhysicalActionChangeset.
    $sql = <<"EOSQL";
CREATE TABLE
    PhysicalActionSchedule (
        schedule_id INTEGER PRIMARY KEY,
        action_id   INTEGER NOT NULL,
        $pa_sql
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # PhysicalActionChangeset is a stoarge place for extra changesets
    # in the timeslice.  These deferred items are reloaded into
    # PhysicalActionSchedule after the git commit happens, so that
    # git changesets can be synthesized from them.
    $sql = <<"EOSQL";
CREATE TABLE
    PhysicalActionChangeset (
        schedule_id INTEGER PRIMARY KEY,
        action_id   INTEGER NOT NULL,
        $pa_sql
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # PhysLabel contains label data for LABEL actions
    $sql = <<"EOSQL";
CREATE TABLE
    PhysLabel (
        action_id   INTEGER PRIMARY KEY,
        label TEXT NOT NULL
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # The PhysicalActionLabel table stores PhysicalActionSchedule
    # label actions which must be deferred until after the master
    # branch is built, because not doing so breaks the model for shared
    # files.
    $sql = <<"EOSQL";
CREATE TABLE
    PhysicalActionLabel (
        schedule_id INTEGER PRIMARY KEY,
        action_id   INTEGER NOT NULL,
        $pa_sql
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # The LabelBookmark table stores the HEAD commit for PhysicalActionLabel
    # as well as the git image at the time of the label.
    $sql = <<"EOSQL";
CREATE TABLE
    LabelBookmark (
        label_id   INTEGER PRIMARY KEY,
        schedule_id INTEGER NOT NULL REFERENCES PhysicalActionLabel (schedule_id),
        head_id TEXT NOT NULL,
        git_image TEXT NOT NULL
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # The PhysicalActionRetired table archives PhysicalActionSchedule items
    # that have been run (e.g. done something to the repository).
    $sql = <<"EOSQL";
CREATE TABLE
    PhysicalActionRetired (
        retired_id INTEGER PRIMARY KEY,
        commit_id INTEGER NOT NULL,
        schedule_id INTEGER NOT NULL,
        action_id   INTEGER NOT NULL,
        $pa_sql
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE INDEX
    PhysicalAction_IDX1 ON PhysicalAction (
        timestamp   ASC
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE INDEX
    PhysicalAction_IDX2 ON PhysicalAction (
        physname   ASC,
        actiontype ASC
    )
EOSQL

    $gCfg{dbh}->do($sql);

    # The SystemInfo table stores checkpoint data for the application
    # for resume.
    my @cfgitems;
    foreach my $param (@system_info_params) {
        my($field, $type);
        while (($field, $type) = each %$param) {
            push @cfgitems, "$field $type";
        }
    }
    my $fielddef = join(', ', @cfgitems);

    $sql = <<"EOSQL";
CREATE TABLE
    SystemInfo (
        $fielddef
    )
EOSQL

    $gCfg{dbh}->do($sql);

    @cfgitems = ();
    foreach my $param (@system_info_params) {
        push @cfgitems, keys %$param;
    }

    my $fields = join(', ', @cfgitems);
    my $args = join(', ', ('NULL') x (scalar @cfgitems));

    $sql = <<"EOSQL";
INSERT INTO
    SystemInfo ($fields)
VALUES
    ($args)
EOSQL

    $gCfg{dbh}->do($sql);

}  #  End InitSysTables

###############################################################################
#  ReloadSysTables
###############################################################################
sub ReloadSysTables {

    my @cfgitems;
    foreach my $param (@system_info_params) {
        push @cfgitems, keys %$param;
    }

    my $row = $gCfg{dbh}->selectall_hashref('SELECT * FROM SystemInfo', \@cfgitems);
    $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
    eval {
        my($field, $val);
        while (($field, $val) = each %$row) {
            if (defined($gCfg{$field})) { # allow user to override saved vals
                $gCfg{dbh}->do("UPDATE SystemInfo SET $field = '$gCfg{$field}'");
            } else {
                $gCfg{$field} = $val;
            }
        }
    };
    if ($@) {
        warn "Transaction aborted because $@";
        eval { $gCfg{dbh}->rollback };
        die "Failed to reload sys tables";
    } else {
        $gCfg{dbh}->commit;
    }

    &SetSystemTask($gCfg{task});

}  #  End ReloadSysTables

###############################################################################
#  Initialize
###############################################################################
sub Initialize {
    $| = 1;

    GetOptions(\%gCfg,'vssdir=s','tempdir=s','repo=s','resume','verbose',
               'debug','timing+','task=s','revtimerange=i','ssphys=s',
               'encoding=s','author_info=s');

    &GiveHelp("Must specify --vssdir") if !defined($gCfg{vssdir});
    &GiveHelp("Must specify --author_info") if !defined($gCfg{author_info});
    $gCfg{tempdir} = $gCfg{tempdir} // TEMPDIR;
    $gCfg{repo} = abs_path($gCfg{repo} // REPO);
    $gCfg{vssdir} = abs_path($gCfg{vssdir});
    $gCfg{vssdatadir} = File::Spec->catdir($gCfg{vssdir}, 'data');
    $gCfg{revtimerange} = REVTIMERANGE unless defined($gCfg{revtimerange}) && $gCfg{revtimerange} > 0;

    if (! -d $gCfg{repo}) {
        mkdir($gCfg{repo});
    }

    if (! -d File::Spec->catdir($gCfg{repo}, '.git')) {
        Git::Repository->run( init => $gCfg{repo} );
    }

    # set up these items now
    $git_image{"@{[VSSDB_ROOT]}"} = $gCfg{repo};
    $gCfg{exclude} = File::Spec->catfile($gCfg{repo}, '.git', 'info', 'exclude');
    $repo_re = qr/^\Q$gCfg{repo}\E./; # XXX not portable

    if (! -d $gCfg{vssdatadir}) {
        die "The VSS database '$gCfg{vssdir}' "
            . "does not appear to be a valid VSS database, as there's no 'data' directory.";
    }

    if (defined($gCfg{author_info}) && ! -r $gCfg{author_info}) {
        die "author_info file '$gCfg{author_info}' is not readable";
    } else {
        open my $info, "<$gCfg{author_info}" or die "Could not open $gCfg{author_info}: $!";
        my $err = 0;

        while (<$info>) {
            my ($username, $author, $author_email) = split(/\t/);
            if (defined $username) {
                if ($username eq '') {
                    ++$err;
                    say "Empty username";
                }

                if (!defined $author) {
                    ++$err;
                    say "Undefined author for username `$username'";
                } elsif ($author eq '') {
                    ++$err;
                    say "Empty author for username `$username'";
                }

                if (!defined $author_email) {
                    ++$err;
                    say "Undefined author email for username `$username'";
                } elsif ($author_email eq '') {
                    ++$err;
                    say "Empty author email for username `$username'";
                }
            }

            $author_map->{$username} = { name => $author, email => $author_email };
        }
        close $info;

        die "author file '$gCfg{author_info}' had errors." if $err;
    }

    $gCfg{sqlitedb} = File::Spec->catfile($gCfg{tempdir}, 'vss_data.db');

    $gCfg{encoding} = $gCfg{encoding} // ENCODING;

    # All sorts of working data placed here
    mkdir $gCfg{tempdir} unless (-d $gCfg{tempdir});

    # Directories for holding VSS revisions
    $gCfg{vssdata} = File::Spec->catdir($gCfg{tempdir}, 'vssdata');

    # Directory for implementing file share/pin/branch.
    # All VSS_FILE entries, not just those shared/pinned will be linked here.
    $gCfg{links} = File::Spec->catdir($gCfg{tempdir}, 'links');

    # Directory for implementing file delete/restore for directories
    # All deleted VSS_PROJECT entries get moved here while deleted
    $gCfg{deleted} = File::Spec->catdir($gCfg{tempdir}, 'deleted');

    $gCfg{task} = $gCfg{task} // TASK_INIT;
    $gCfg{resume} = 1 if ($gCfg{task} ne TASK_INIT);

    if ($gCfg{resume} && !-e $gCfg{sqlitedb}) {
        warn "WARNING: --resume set but no database exists; "
            . "starting new conversion...";
        $gCfg{resume} = 0;
    }

    if ($gCfg{debug}) {
        $gCfg{verbose} = 1;
    }
    $gCfg{timing} = $gCfg{timing} // 0;
    $gCfg{ssphys} = $gCfg{ssphys} // SSPHYS;

    $gCfg{starttime} = scalar localtime($^T);

    $gCfg{errortasks} = [];

    {
        no warnings 'once';
        $gCfg{usingExe} = (defined($PerlApp::TOOL));
    }

    # Files for various puposes.  The 'keep' file is to
    # force git to keep directory files with no other files
    # in them around.
    $gCfg{keepFile} = File::Spec->catfile($gCfg{tempdir}, KEEP_FILE);
    $gCfg{destroyedFile} = File::Spec->catfile($gCfg{tempdir},'destroyed.txt');
    $gCfg{deletedFile} = File::Spec->catfile($gCfg{tempdir},'deleted.txt');
    $gCfg{indeterminateFile} = File::Spec->catfile($gCfg{tempdir},'indeterminate.txt');

    $gCfg{commit_id} = 1;

    ### Don't go past here if resuming a previous run ###
    if ($gCfg{resume}) {
        return 1;
    }

    rmtree($gCfg{vssdata}) if (-e $gCfg{vssdata});
    mkdir $gCfg{vssdata};
    rmtree($gCfg{links}) if (-e $gCfg{links});
    mkdir $gCfg{links};

    rmtree($gCfg{deleted}) if (-e $gCfg{deleted});
    mkdir $gCfg{deleted};

    &WriteDestroyedPlaceholderFiles();
}  #  End Initialize

###############################################################################
#  GiveHelp
###############################################################################
sub GiveHelp {
    my($msg) = @_;
    my @states = ();
    my @states_line = ();
    my $line = '';

    # columnate the task states
    foreach my $e (@joblist) {
        push @states, $e->{task};
    }
    foreach my $e (@states) {
        if (!((length($e) + 1 + length($line)) > 50)) {
            if (length($line) == 0) {
                $line = $e;
            } else {
                $line .= ' ' . $e;
            }
        } else {
            push @states_line, $line;
            $line = $e;
        }
    }
    push @states_line, $line;
    $line = join q{\n}, @states_line;
    my @output = `printf "$line" | column -c 50 -t | awk '{printf("%24s%-50s\\n", " ", \$0);}'`;
    $line = join "", @output;

    $msg ||= 'Online Help';

    print <<"EOTXT";

$msg

USAGE: perl @{[PROGNAME]}.pl --vssdir <dir> --author_info <file> [options]

REQUIRED PARAMETERS:
    --vssdir <dir>  : Directory where VSS database is located. This should be
                      the directory in which the "srcsafe.ini" file is located.
    --author_info <file>   : Tab separated file of <username> <author> <author_email>
                             where <username> is a VSS username

OPTIONAL PARAMETERS:
    --ssphys <path>   : Full path to @{[SSPHYS]} program; uses PATH otherwise
    --tempdir <dir>   : Work directory to use during conversion;
                        default is '@{[TEMPDIR]}'.  Must be on the same filesystem
                        as --repo.
    --repo <directory> : specify the git repository to use;
                         default is '@{[REPO]}'.  If it does not exist, it
                         will be created.  If it is not initalized, it will be initialized.
                         It may be previously initialized with 'git init'
                         and contain appropriate settings files
                         (e.g, .gitignore, .gitattributes, etc.) for the migration.
                         Must be on the same filesystem as --tempdir.
    --revtimerange <sec> : specify the maximum time difference (in seconds)
                           between two VSS actions that are treated as one git commit;
                           default is @{[REVTIMERANGE]} seconds.  Must be > 0.

    --resume          : Resume a failed or aborted previous run
    --task <task>     : specify the task to resume; task is one of the following
$line
    --verbose         : Print more info about the items being processed
    --debug           : Print lots of debugging info.
    --timing          : Show timing information during various steps
    --encoding        : Specify the encoding used in VSS;
                        Default is '@{[ENCODING]}'
EOTXT

    exit(1);
}  #  End GiveHelp

###############################################################################
#  WriteDestroyedPlaceholderFiles
###############################################################################
sub WriteDestroyedPlaceholderFiles {
    open (DEST, ">$gCfg{destroyedFile}");
    print DEST <<"EOTXT";
@{[PROGNAME]} has determined that this file has been destroyed in VSS history.
@{[PROGNAME]} cannot retrieve it, since it no longer exists in the VSS database.
EOTXT
    close(DEST);

    open (DEST, ">$gCfg{deletedFile}");
    print DEST <<"EOTXT";
@{[PROGNAME]} has determined that this file has been deleted in VSS history.
@{[PROGNAME]} cannot retrieve it, since it no longer exists in the VSS database.
EOTXT
    close(DEST);

    open (DEST, ">$gCfg{indeterminateFile}");
    print DEST <<"EOTXT";
@{[PROGNAME]} cannot determine what has happened to this file.
@{[PROGNAME]} was not able to retrieve it. This file was possibly lost
due to corruption in the VSS database.
EOTXT
    close(DEST);

    open (DEST, ">$gCfg{keepFile}");
    close(DEST);
}

sub TimestampLimits {
    my($sql);

    $sql = <<"EOSQL";
SELECT
    MIN(timestamp), MAX(timestamp)
FROM
    PhysicalAction
EOSQL

    ($gCfg{mintime}, $gCfg{maxtime}) = $gCfg{dbh}->selectrow_array($sql);
}

sub DestroyedHash {
    my $repo = Git::Repository->new(work_tree => "$gCfg{repo}");
    $repo->setlog($gCfg{debug});
    $gCfg{destroyedHash} = $repo->logrun('hash-object' => '--',  abs_path($gCfg{destroyedFile}));
}

sub InsertPhysicalActionChangeset {
    my $tmp_sth = $gCfg{dbh}->prepare_cached('INSERT INTO PhysicalActionSchedule '
                                             . 'SELECT * FROM PhysicalActionChangeset');
    my $tmp2_sth = $gCfg{dbh}->prepare_cached('DELETE FROM PhysicalActionChangeset');

    $tmp_sth->execute();
    $tmp2_sth->execute();
    $tmp_sth->finish();
    $tmp2_sth->finish();
}

sub ResetTimestampFromSchedule {
    my $tmp_sth = $gCfg{dbh}->prepare_cached('SELECT timestamp '
                                             . 'FROM PhysicalActionSchedule '
                                             . 'WHERE schedule_id = '
                                             . '(SELECT MIN(schedule_id) FROM PhysicalActionSchedule)');

    $tmp_sth->execute();
    my ($timestamp) = $tmp_sth->fetchrow_array();
    $tmp_sth->finish();

    return $timestamp;
}

###############################################################################
#  SchedulePhysicalActions
###############################################################################
sub SchedulePhysicalActions {
    my($timestamp) = @_;
    state $index = 0;

    # We must schedule, since timestamp is not fine enough resolution,
    # that some events happen before they should. So the timeline is
    # fixed here, if possible.

    # PhysicalActionSchedule should be empty at this point
    my $tmp_sth = $gCfg{dbh}->prepare_cached('SELECT COUNT(*) FROM PhysicalActionChangeset',
                                             { dbi_dummy => __FILE__.__LINE__ });
    $tmp_sth->execute();
    my ($changeset_count) = $tmp_sth->fetchrow_array();
    $tmp_sth->finish();
    my $sth = $gCfg{dbh}->prepare_cached('INSERT INTO PhysicalActionSchedule '
                                         . 'SELECT NULL AS schedule_id, * '
                                         . 'FROM PhysicalAction '
                                         . 'WHERE timestamp >= ? '
                                         . '  AND timestamp < ? '
                                         . '  AND action_id NOT IN '
                                         . '  (SELECT action_id FROM PhysicalActionSchedule '
                                         . '   UNION ALL SELECT action_id FROM PhysicalActionRetired) '
                                         . 'ORDER BY timestamp ASC, priority ASC, '
                                         . 'vss_phys_to_num(physname) ASC, parentdata ASC',
                                         { dbi_dummy => __FILE__.__LINE__ });
    if (defined $changeset_count && $changeset_count > 0) {
        # We have unused data from the last scheduling pass, let's use it.
        &InsertPhysicalActionChangeset();

        # need to reset time, since there may be two commits in the same timestamp
        $timestamp = &ResetTimestampFromSchedule();

    }

    # This slides the window down.
    my $should_schedule = $sth->execute($timestamp, $timestamp+$gCfg{revtimerange});

    if (defined $should_schedule && $should_schedule > 0) {
        say "timestamp range: $timestamp - " . ($timestamp+$gCfg{revtimerange}) if $gCfg{debug};
        &CheckAffinity();
    }

    &GetOneChangeset($timestamp);
    $sth->finish();
}

###############################################################################
#  CheckAffinity
###############################################################################
sub CheckAffinity {
    my($sth, $rows);

    # Attempt to schedule rows where there's multiple rows having the same
    # timestamp.
    # Sometimes when rows share a timestamp, it's
    # obvious when looking at other fields (author, comment)
    # that they should be reordered
    my $ath = $gCfg{dbh}->prepare_cached('SELECT DISTINCT timestamp '
                                         . 'FROM PhysicalActionSchedule '
                                         . 'ORDER BY timestamp',
                                         { dbi_dummy => __FILE__.__LINE__ });
    $ath->execute();
    my $timestamps = $ath->fetchall_arrayref();
    foreach my $t (@$timestamps) {
        my $timestamp = $t->[0];
        my $rowcount;
        my $tmp_sth = $gCfg{dbh}->prepare_cached('SELECT COUNT(*) FROM PhysicalActionSchedule '
                                                 . ' WHERE timestamp = ? ORDER BY schedule_id',
                                                 { dbi_dummy => __FILE__.__LINE__ });
        $tmp_sth->execute($timestamp);
        ($rowcount) = $tmp_sth->fetchrow_array();
        $tmp_sth->finish();

        if ($rowcount > 1) {
            $gCfg{dbh}->do('CREATE TEMPORARY TABLE tmp_affinity AS '
                           . ' SELECT 0 AS affinity, * FROM PhysicalActionSchedule '
                           . ' WHERE timestamp = ? ORDER BY schedule_id', undef, $timestamp);

            # grab identifying data
            $sth = $gCfg{dbh}->prepare('SELECT schedule_id, action_id '
                                       . 'FROM tmp_affinity ORDER BY schedule_id');
            $sth->execute();
            my $ooo_data = $sth->fetchall_arrayref({});

            # In this scheme a negative value means pull up in the schedule,
            # 0 means no change, positive, move down the schedule.

            # check affinity with timestamp not equal to this one
            # of previously scheduled row
            $sth = $gCfg{dbh}->prepare_cached('SELECT * FROM PhysicalActionSchedule '
                                              . 'WHERE schedule_id = '
                                              . '   (SELECT MAX(schedule_id) '
                                              . '    FROM PhysicalActionSchedule '
                                              . '    WHERE timestamp = '
                                              . '          (SELECT MAX(timestamp) '
                                              . '           FROM PhysicalActionSchedule '
                                              . '           WHERE timestamp < ?)) LIMIT 1',
                                              { dbi_dummy => __FILE__.__LINE__ });
            $sth->execute($timestamp);
            my $lrow;
            while (defined($lrow = $sth->fetchrow_hashref())) {
                &UpdateRowAffinity($lrow,-1);
            }
            $sth->finish();

            # check affinity with timestamp not equal to this one
            # of next row. This operation might not be a good idea --
            # these really aren't scheduled yet!
            $sth = $gCfg{dbh}->prepare_cached('SELECT * FROM PhysicalActionSchedule '
                                              . 'WHERE schedule_id = '
                                              . '   (SELECT MIN(schedule_id) '
                                              . '    FROM PhysicalActionSchedule '
                                              . '    WHERE timestamp = '
                                              . '          (SELECT MIN(timestamp) '
                                              . '           FROM PhysicalActionSchedule '
                                              . '           WHERE timestamp > ?)) LIMIT 1',
                                              { dbi_dummy => __FILE__.__LINE__ });
            $sth->execute($timestamp);
            while (defined($lrow = $sth->fetchrow_hashref())) {
                &UpdateRowAffinity($lrow,1);
            }
            $sth->finish();

            # sort using affinity first
            $sth = $gCfg{dbh}->prepare('SELECT schedule_id, action_id '
                                       . 'FROM tmp_affinity '
                                       . 'ORDER BY affinity ASC, schedule_id ASC');
            $sth->execute();
            my $ino_data = $sth->fetchall_arrayref({});

            # see if the ordering should change
            my @oids = map { $_->{schedule_id} } @$ooo_data;
            my @iids = map { $_->{schedule_id} } @$ino_data;

            if (!(@oids ~~ @iids)) {
                say "affinity changed" if $gCfg{debug};
                $tmp_sth = $gCfg{dbh}->prepare("UPDATE tmp_affinity SET schedule_id = ? "
                                               ."WHERE schedule_id = ? "
                                               ."AND action_id = ?");

                my $i = 0;
                foreach my $o (@oids) {
                    my $m = $ino_data->[$i];
                    if ($o != $m->{schedule_id}) {
                        $tmp_sth->execute($o, $m->{schedule_id}, $m->{action_id});
                    }
                    ++$i;
                }

                # clear out the out of order records
                $gCfg{dbh}->do('DELETE FROM PhysicalActionSchedule '
                               . 'WHERE schedule_id '
                               . '  IN (SELECT schedule_id FROM tmp_affinity)');

                # SQLite can't drop columns, so we have this workaround...
                my @pas_ary;
                foreach my $param (@physical_action_params) {
                    push @pas_ary, keys %$param;
                }
                unshift @pas_ary, ('schedule_id', 'action_id');
                my $pas_params_sql = join q{,}, @pas_ary;

                $gCfg{dbh}->do("INSERT INTO PhysicalActionSchedule "
                               . "SELECT $pas_params_sql FROM tmp_affinity");
            }
            $gCfg{dbh}->do('DROP TABLE tmp_affinity');
        }
    }
    $ath->finish();
}

###############################################################################
#  UpdateRowAffinity
###############################################################################
sub UpdateRowAffinity {
    my ($lrow, $direction) = @_;

    my $rth = $gCfg{dbh}->prepare('UPDATE tmp_affinity SET affinity = affinity+? WHERE author = ?');
    $rth->execute($direction, $lrow->{author});

    if (defined $lrow->{comment}) {
        $rth = $gCfg{dbh}->prepare('UPDATE tmp_affinity SET affinity = affinity+? WHERE comment = ?');
        $rth->execute($direction, $lrow->{comment});
    } else {
        $rth = $gCfg{dbh}->prepare('UPDATE tmp_affinity SET affinity = affinity+? WHERE comment IS NULL');
        $rth->execute($direction);
    }

    if ($lrow->{actiontype} eq ACTION_LABEL) {
        $rth = $gCfg{dbh}->prepare('SELECT label FROM PhysLabel WHERE action_id = ?');
        $rth->execute($lrow->{action_id});
        ($lrow->{label}) = $rth->fetchrow_array();

        if (defined $lrow->{label}) {
            my $d2 = $direction*2; # more heavily weight these
            $rth = $gCfg{dbh}->prepare("UPDATE tmp_affinity SET affinity = affinity+? "
                                       . "WHERE actiontype = '@{[ACTION_LABEL]}' "
                                       . "AND action_id IN (SELECT action_id FROM PhysLabel WHERE label = ?)");
            $rth->execute($d2, $lrow->{label});
        }
    }
 }

sub GetOneChangesetLog {
    my($msg, $schedule_id, $dbg_sth) = @_;
    my $desc = $schedule_id // 'undef';

    $dbg_sth->execute();
    my ($dbgcnt) = $dbg_sth->fetchrow_array();
    say "$msg $desc rows: $dbgcnt";
}

###############################################################################
#  GetOneChangeset
###############################################################################
sub GetOneChangeset {
    my($timestamp) = @_;
    my $isth;
    my $dsth;
    my $dbgcnt;
    my $dbg_sth;

    $isth = $gCfg{dbh}->prepare_cached('INSERT INTO PhysicalActionChangeset '
                                       . 'SELECT * FROM PhysicalActionSchedule WHERE schedule_id >= ?',
                                       { dbi_dummy => __FILE__.__LINE__ },
                                       1);
    $dsth = $gCfg{dbh}->prepare_cached('DELETE FROM PhysicalActionSchedule WHERE schedule_id >= ?',
                                       { dbi_dummy => __FILE__.__LINE__ },
                                       1);

    # Now that we have a reasonable ordering of events, look for
    # exactly one changeset starting at this timestamp

    # Trim down the schedule first by:
    #
    # * different author
    # * different comment
    # * group similar LABEL actions together
    # * most actions on a directory
    # * same file touched more than once

    if ($gCfg{debug}) {
        $dbg_sth = $gCfg{dbh}->prepare_cached('SELECT COUNT(*) FROM PhysicalActionSchedule',
                                              { dbi_dummy => __FILE__.__LINE__ });
        $dbg_sth->execute();
        ($dbgcnt) = $dbg_sth->fetchrow_array();
        say "scheduling timestamp $timestamp with $dbgcnt rows";
    }

    # Any leftovers are moved to PhysicalActionChangeset
    # for subsequent calls to SchedulePhysicalActions
    my $schedule_id;

    # dump all entries incuding and after the first mismatch of author
    # It's at least two changesets in this case.
    my $tmp_sth = $gCfg{dbh}->prepare_cached('SELECT schedule_id '
                                             . 'FROM PhysicalActionSchedule '
                                             . 'WHERE author NOT IN '
                                             . '(SELECT author '
                                             . ' FROM PhysicalActionSchedule '
                                             . ' WHERE timestamp = ? ORDER BY schedule_id LIMIT 1) '
                                             . 'ORDER BY schedule_id LIMIT 1',
                                             { dbi_dummy => __FILE__.__LINE__ });

    $tmp_sth->execute($timestamp);
    ($schedule_id) = $tmp_sth->fetchrow_array();
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }
    $tmp_sth->finish();

    &GetOneChangesetLog("scheduling author ", $schedule_id, $dbg_sth) if $gCfg{debug};

    # dump all entries incuding and after the first mismatch of comments
    # N.B. comments may be NULL
    # Again, it's at least two changesets in this case.
    $tmp_sth = $gCfg{dbh}->prepare_cached('SELECT MIN(B.schedule_id) '
                                          . 'FROM (SELECT comment FROM PhysicalActionSchedule '
                                          . '      ORDER BY schedule_id LIMIT 1) AS A '
                                          . 'CROSS JOIN (SELECT schedule_id, comment '
                                          . '            FROM PhysicalActionSchedule) AS B '
                                          . 'WHERE (A.comment IS NULL AND B.comment IS NOT NULL '
                                          . '       OR A.comment IS NOT NULL AND B.comment IS NULL '
                                          . '       OR A.comment IS NOT NULL AND B.comment IS NOT NULL '
                                          . '          AND A.comment != B.comment)',
                                          { dbi_dummy => __FILE__.__LINE__ });

    $tmp_sth->execute();
    ($schedule_id) = $tmp_sth->fetchrow_array();
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }
    $tmp_sth->finish();

    &GetOneChangesetLog("scheduling comment ", $schedule_id, $dbg_sth) if $gCfg{debug};

    # Label filter part 1
    # When the first item on the schedule is (or is not) a LABEL, remove the first
    # non-LABEL (or LABEL) from the schedule and any subsequent entries
    $tmp_sth = $gCfg{dbh}->prepare_cached("SELECT MIN(B.schedule_id) "
                                          . "FROM (SELECT actiontype FROM PhysicalActionSchedule "
                                          . "      ORDER BY schedule_id LIMIT 1) AS A "
                                          . "CROSS JOIN (SELECT schedule_id, actiontype "
                                          . "            FROM PhysicalActionSchedule) AS B "
                                          . "WHERE (A.actiontype = '@{[ACTION_LABEL]}' "
                                          . "       AND B.actiontype != '@{[ACTION_LABEL]}') "
                                          . "   OR (A.actiontype != '@{[ACTION_LABEL]}' "
                                          . "       AND B.actiontype = '@{[ACTION_LABEL]}')",
                                          { dbi_dummy => __FILE__.__LINE__ });

    $tmp_sth->execute();
    ($schedule_id) = $tmp_sth->fetchrow_array();
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }
    $tmp_sth->finish();

    &GetOneChangesetLog("scheduling label pre ", $schedule_id, $dbg_sth) if $gCfg{debug};

    # dump all entries incuding and after the first mismatch of labels
    # Again, it's at least two labels. Even though there are no changes,
    # in a label how we are handling labels makes separating differing
    # labels into a changeset important.
    # This should be sufficient to isolate LABEL actions, since other
    # actions won't have label data.
    $tmp_sth = $gCfg{dbh}->prepare_cached("SELECT MIN(B.schedule_id) "
                                          . "FROM (SELECT X.actiontype AS actiontype, Y.label AS label "
                                          . "      FROM PhysicalActionSchedule AS X, PhysLabel AS Y "
                                          . "      WHERE X.action_id = Y.action_id "
                                          . "      ORDER BY X.schedule_id LIMIT 1) AS A "
                                          . "CROSS JOIN (SELECT X.schedule_id AS schedule_id, X.actiontype AS actiontype, Y.label AS label "
                                          . "            FROM PhysicalActionSchedule AS X, PhysLabel AS Y "
                                          . "            WHERE X.action_id = Y.action_id) AS B "
                                          . "WHERE A.label != B.label",
                                          { dbi_dummy => __FILE__.__LINE__ });

    $tmp_sth->execute();
    ($schedule_id) = $tmp_sth->fetchrow_array();
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }
    $tmp_sth->finish();

    &GetOneChangesetLog("scheduling label ", $schedule_id, $dbg_sth) if $gCfg{debug};

    # * most directory actions
    # If the topmost scheduled action is one of the actions in the set
    # delete everything else from the schedule.  Otherwise if one is anywhere
    # else on the schedule, remove it and everything after it.
    $tmp_sth = $gCfg{dbh}->prepare_cached("SELECT MIN(CASE X.schedule_id "
                                          . "           WHEN (SELECT MIN(schedule_id) FROM PhysicalActionSchedule) "
                                          . "           THEN X.schedule_id+1 "
                                          . "           ELSE X.schedule_id "
                                          . "           END) "
                                          . "FROM PhysicalActionSchedule AS X, PhysItemtype AS Y "
                                          . "WHERE X.physname = Y.physname "
                                          . "AND Y.itemtype = @{[VSS_PROJECT]} AND X.actiontype IN "
                                          . "('@{[ACTION_RESTOREDPROJECT]}', '@{[ACTION_RENAME]}', "
                                          . "'@{[ACTION_DELETE]}', '@{[ACTION_DESTROY]}', '@{[ACTION_RECOVER]}', "
                                          . "'@{[ACTION_RESTORE]}', '@{[ACTION_MOVE_TO]}', '@{[ACTION_MOVE_FROM]}')",
                                          { dbi_dummy => __FILE__.__LINE__ });

    $tmp_sth->execute();
    ($schedule_id) = $tmp_sth->fetchrow_array();
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }
    $tmp_sth->finish();

    &GetOneChangesetLog("scheduling dir actions ", $schedule_id, $dbg_sth) if $gCfg{debug};

    # * same file touched more than once
    # SHARE and BRANCH are pretty benign, other actions potentially
    # change files.
    $tmp_sth = $gCfg{dbh}->prepare_cached("SELECT MIN(A.schedule_id) "
                                          . "FROM (SELECT X.schedule_id AS schedule_id, X.actiontype AS actiontype, X.physname AS physname "
                                          . "      FROM PhysicalActionSchedule AS X, PhysItemtype AS Y "
                                          . "      WHERE X.physname = Y.physname AND Y.itemtype = @{[VSS_FILE]} "
                                          . "      AND X.parentdata != 0"
                                          . "      UNION ALL SELECT X.schedule_id AS schedule_id, X.actiontype AS actiontype, X.physname AS physname "
                                          . "      FROM PhysicalActionSchedule AS X, PhysItemtype AS Y "
                                          . "      WHERE X.physname = Y.physname AND Y.itemtype = @{[VSS_FILE]} "
                                          . "      AND X.parentdata = 0"
                                          . "      AND X.actiontype IN ('@{[ACTION_COMMIT]}', '@{[ACTION_LABEL]}')"
                                          . "      ORDER BY schedule_id) AS A "
                                          . "CROSS JOIN "
                                          . "     (SELECT X.schedule_id AS schedule_id, X.actiontype AS actiontype, X.physname AS physname "
                                          . "      FROM PhysicalActionSchedule AS X, PhysItemtype AS Y "
                                          . "      WHERE X.physname = Y.physname AND Y.itemtype = @{[VSS_FILE]} "
                                          . "      AND X.parentdata != 0"
                                          . "      UNION ALL SELECT X.schedule_id AS schedule_id, X.actiontype AS actiontype, X.physname AS physname "
                                          . "      FROM PhysicalActionSchedule AS X, PhysItemtype AS Y "
                                          . "      WHERE X.physname = Y.physname AND Y.itemtype = @{[VSS_FILE]} "
                                          . "      AND X.parentdata = 0"
                                          . "      AND X.actiontype IN ('@{[ACTION_COMMIT]}', '@{[ACTION_LABEL]}')"
                                          . "      ORDER BY schedule_id) AS B "
                                          . "WHERE A.physname = B.physname AND A.schedule_id > B.schedule_id "
                                          . "AND A.actiontype NOT IN ('@{[ACTION_SHARE]}', '@{[ACTION_BRANCH]}')",
                                          { dbi_dummy => __FILE__.__LINE__ });
    $tmp_sth->execute();
    ($schedule_id) = $tmp_sth->fetchrow_array();
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }
    $tmp_sth->finish();

    &GetOneChangesetLog("scheduling same file touched ", $schedule_id, $dbg_sth) if $gCfg{debug};

    if ($gCfg{debug}) {
        $dbg_sth->finish();
    }
}

# update the image name mapping when files/directories are moved
sub MoveProject {
    my($oldpath, $newpath, $git_image) = @_;
    my $sep = "/"; # XXX not platform independent
    my $oldpath_re = qr/^\Q${oldpath}${sep}\E(.*)$/;
    my $oldpath_nosep_re = qr/^\Q${oldpath}\E$/;

    foreach my $key (keys %{$git_image}) {
        # have to be a little careful here with VSS_PROJECTs...
        if (ref($git_image->{$key})) {
            # substitute for VSS_FILEs
            s/$oldpath_re/${newpath}${sep}$1/ for @{$git_image->{$key}};
        } elsif ($git_image->{$key} =~ m/$oldpath_re/) {
            $git_image->{$key} =~ s/$oldpath_re/${newpath}${sep}$1/;
        } elsif ($git_image->{$key} =~ m/$oldpath_nosep_re/) {
            $git_image->{$key} = ${newpath};
        }
    }
}

sub RmProject {
    my($path, $git_image) = @_;
    my $sep = "/"; # XXX not platform independent
    my $path_re = qr/^\Q${path}${sep}\E/;
    my $path_nosep_re = qr/^\Q${path}\E$/;

#    say "git_image: " . Dumper($git_image) if $gCfg{debug};

    foreach my $key (keys %{$git_image}) {
        if (ref($git_image->{$key})) {
            @{$git_image->{$key}} = grep {!/$path_re/} @{$git_image->{$key}};
            if (scalar @{$git_image->{$key}} == 0) {
                delete $git_image->{$key};
            }
        } elsif ($git_image->{$key} =~ m/$path_re|$path_nosep_re/) {
            delete $git_image->{$key};
        }
    }
}

# invoke git one action at a time
sub UpdateGitRepository {
    my($row, $parentpath, $path, $git_image, $repo) = @_;

    my @delete_actions = (ACTION_DELETE, ACTION_DESTROY);
    my @restore_actions = (ACTION_RESTORE, ACTION_RESTOREDPROJECT);

    eval {
        my $warn_msg = "UpdateGitRepository: $row->{actiontype} $row->{itemtype} ";
        for ($row->{itemtype}) {
            when (VSS_PROJECT) {
                for ($row->{actiontype}) {
                    when (ACTION_ADD) {
                        if (! -d $path) {
                            make_path($path);
                            if (!copy($gCfg{keepFile}, $path)) {
                                warn "$warn_msg copy $!";
                            } else {
                                $git_image->{$row->{physname}} = $path;
                                $repo->logrun(add => '--',  $path);
                                &RemoveKeep($repo, $parentpath);
                            }
                        }
                    }
                    when (@restore_actions) {
                        # XXX need example
                        # I don't think anything needs to be done here anyway
                        # but I could be mistaken.
                    }
                    when (ACTION_RENAME) {
                        my $newpath = File::Spec->catdir($parentpath, $row->{info});
                        &DoMoveProject($repo, $path, $newpath, $git_image, 1);
                        &MoveExcludes($path, $newpath);
                    }
                    when (ACTION_MOVE_TO) {
                        # physname directory inode to move
                        # parentphys physname's parent directory
                        # info destination directory path
                        my $newpath = File::Spec->catdir($gCfg{repo}, $row->{info});

                        &DoMoveProject($repo, $path, $newpath, $git_image, 1);
                    }
                    when (ACTION_MOVE_FROM) {
                        # physname moved directory inode
                        # parentphys destination's parent directory
                        # info source directory path
                        my $oldpath = File::Spec->catdir($gCfg{repo}, $row->{info});

                        &DoMoveProject($repo, $oldpath, $path, $git_image, 0);
                        &MoveExcludes($oldpath, $path);
                    }
                    when (@delete_actions) {
                        if (-d $path) {
                            &RmProject($path, $git_image);
                            &RewriteExcludes($path, 1);
                            &GitRm($repo, $parentpath, $path, $row->{itemtype}, $row->{actiontype}, $row->{action_id});
                        }
                    }
                    when (ACTION_RECOVER) {
                        &GitRecover($repo, $row, $path, $git_image);
                    }
                    when (ACTION_LABEL) {
                        &DeferLabel($row, $repo);
                    }
                }
            }
            when (VSS_FILE) {
                my $link_file = File::Spec->catfile($gCfg{links}, $row->{physname});
                for ($row->{actiontype}) {
                    when (ACTION_ADD) {
                        # recorded in both the parent and child
                        if ($row->{parentdata}) {
                            if (! -f $path) {
                                # In the case of a destroyed file there's only the parent record
                                # we'll go ahead and add the file in case the child record is blown away
                                # by something.

                                if (! -f  $link_file) {
                                    my $tmp_sth = $gCfg{dbh}->prepare_cached("SELECT action_id "
                                                                             . "FROM PhysicalAction "
                                                                             . "WHERE physname = ? "
                                                                             . "AND actiontype = '@{[ACTION_DESTROY]}' "
                                                                             . "LIMIT 1",
                                                                             { dbi_dummy => __FILE__.__LINE__ });

                                    $tmp_sth->execute($row->{physname});
                                    my ($action_id) = $tmp_sth->fetchrow_array();
                                    $tmp_sth->finish();
                                    if (!copy((($action_id) ? $gCfg{destroyedFile} : $gCfg{indeterminateFile}),
                                              $link_file)) {  # touch the file
                                        warn "$warn_msg path `$link_file' copy $!";
                                    }
                                    if ($action_id) {
                                        $destroyed_files->{$row->{physname}} = 1;
                                        &AppendExcludeEntry($path);
                                    }
                                }
                                link $link_file, $path;
                                if (!$destroyed_files->{$row->{physname}}) {
                                    $repo->logrun(add => '--',  $path);
                                    &RemoveKeep($repo, $parentpath);
                                }
                                @{$git_image->{$row->{physname}}} = ("$path"); # may be on multiple paths
                            }
                        } elsif (defined $git_image->{$row->{physname}}
                                 && ref($git_image->{$row->{physname}})) {
                            # we have child data here
                            my $is_destroyed;

                            $path = @{$git_image->{$row->{physname}}}[0];
                            my $efile = &ExportVssPhysFile($row->{physname}, $row->{version}, \$is_destroyed);

                            if (defined $efile) {
                                # copy the data to the link
                                if (!copy($efile, $link_file)) {
                                    warn "$warn_msg export `$efile' path `$link_file' copy $!";
                                } else {
                                    if (!$is_destroyed && !$destroyed_files->{$row->{physname}}) {
                                        $repo->logrun(add => '--',  $path);
                                        &RemoveKeep($repo, $parentpath);
                                    } else {
                                        if (!$destroyed_files->{$row->{physname}}) {
                                            $destroyed_files->{$row->{physname}} = 1;
                                        }
                                        &AppendExcludeEntry($path);
                                    }
                                }
                            }
                        } else {
                            # we have child data, but no parent data (yet)
                            # read it out for the link
                            # This step seems to happen chronologically first before
                            # writing the parent info, so they may be in different timestamps
                            my $is_destroyed;
                            my $efile = &ExportVssPhysFile($row->{physname}, $row->{version}, \$is_destroyed);

                            if (defined $efile) {
                                # copy the data to the link
                                if (!copy($efile, $link_file)) {
                                    warn "$warn_msg export `$efile' link path `$link_file' copy $!";
                                }
                                if ($is_destroyed) {
                                    $destroyed_files->{$row->{physname}} = 1;
                                }
                            }
                        }
                    }
                    when (ACTION_RENAME) {
                        # these are only recorded in the parent
                        # Files may be renamed after DELETE(!) through a SHARE apparently
                        # so we need to check for their existence
                        my $newpath = File::Spec->catfile($parentpath, $row->{info});
                        if (-f $path) {
                            # check for renames involving case only
                            if ($path =~ /^\Q$newpath\E$/i) {
                                my $tmp_mv = File::Spec->catfile(dirname($path), MOVE_TMP_FILE);
                                if (!$destroyed_files->{$row->{physname}}) {
                                    $repo->logrun(mv =>  $path,  $tmp_mv);
                                    $repo->logrun(mv =>  $tmp_mv,  $newpath);
                                } else {
                                    if (!move($path, $tmp_mv)) {
                                        warn "$warn_msg path: `$path' tmp: `$tmp_mv' $!";
                                    }
                                    if (!move($tmp_mv, $newpath)) {
                                        warn "$warn_msg tmp: `$tmp_mv' newpath: `$newpath' $!";
                                    }
                                }
                            } else {
                                if (!$destroyed_files->{$row->{physname}}) {
                                    $repo->logrun(mv =>  $path,  $newpath);
                                } else {
                                    if (!move($path, $newpath)) {
                                        warn "$warn_msg path: `$path' newpath: `$newpath' $!";
                                    }
                                }
                            }
                        }

                        # remove the old path, add the new path
                        @{$git_image->{$row->{physname}}} = grep {!/^\Q$path\E$/} @{$git_image->{$row->{physname}}};
                        push @{$git_image->{$row->{physname}}}, $newpath;
                        if ($destroyed_files->{$row->{physname}}) {
                            &RewriteExcludes($path);
                            &AppendExcludeEntry($newpath);
                        }
                    }
                    when (@delete_actions) {
                        # these are only recorded in the parent
                        my $path_re = qr/^\Q$path\E$/;
                        my $unlinked_file = 0;

                        if (-f $path) {
                            my ($link_ino, $path_ino);

                            (undef, $link_ino) = stat($link_file);
                            (undef, $path_ino) = stat($path);

                            @{$git_image->{$row->{physname}}} = grep {!/$path_re/} @{$git_image->{$row->{physname}}};

                            if (scalar @{$git_image->{$row->{physname}}} == 0) {
                                say "$warn_msg deleting git image $row->{physname}" if $gCfg{debug};
                                delete $git_image->{$row->{physname}};
                            }

                            # must check the inode at the path because:
                            # file1 may be DELETEd, file2 ADDed, and file1 DESTROYed.
                            if ($link_ino == $path_ino) {
                                if (!defined $destroyed_files->{$row->{physname}}) {
                                    &GitRm($repo, $parentpath, $path, $row->{itemtype}, $row->{actiontype}, $row->{action_id});
                                } else {
                                    unlink $path;
                                    $unlinked_file = 1;
                                }
                            } elsif ($row->{actiontype} eq ACTION_DESTROY) {
                                my $action_id_del = &LastDeleteTime($row->{physname}, $row->{timestamp});
                                my $delete_loc = File::Spec->catfile($gCfg{deleted}, $action_id_del);
                                my $delete_loc_ino;

                                (undef, $delete_loc_ino) = stat($delete_loc);
                                if ($link_ino == $delete_loc_ino) {
                                    unlink $delete_loc;
                                }
                            }
                        }

                        # deleted files can be recovered, so it doesn't really affect the
                        # link count
                        if ($unlinked_file) {
                            if ($destroyed_files->{$row->{physname}} <= 1) {
                                delete $destroyed_files->{$row->{physname}};
                            } else {
                                --$destroyed_files->{$row->{physname}};
                            }
                            &RewriteExcludes($path);
                        }
                    }
                    when (ACTION_RECOVER) {
                        &GitRecover($repo, $row, $path, $git_image);
                    }
                    when (@restore_actions) {
                        # XXX need example
                        # I don't think anything needs to be done here anyway
                        # but I could be mistaken.
                    }
                    when (ACTION_COMMIT) {
                        # only recorded in the child
                        my $is_destroyed;
                        my $newver = &ExportVssPhysFile($row->{physname}, $row->{version}, \$is_destroyed);

                        if (defined $newver) {

                            if (!copy($newver, $link_file)) {
                                warn "$warn_msg newver `$newver' path `$link_file' copy $!";
                            } else {
                                if (!$is_destroyed) {
                                    $repo->logrun(add => '--',  $path);
                                } else {
                                    if (!$destroyed_files->{$row->{physname}}) {
                                        $destroyed_files->{$row->{physname}} = 1;
                                        &AppendExcludeEntry($path);
                                    }
                                }
                            }
                        }
                    }
                    when (ACTION_SHARE) {
                        # only recorded in parent (but present in child XML)
                        my $oldpath = &SearchForPath($row->{physname}, $git_image);

                        if (! -f $path) {
                            link $oldpath, $path;
                            push @{$git_image->{$row->{physname}}}, $path;
                            if (!$destroyed_files->{$row->{physname}}) {
                                $repo->logrun(add => '--',  $path);
                                &RemoveKeep($repo, $parentpath);
                            } else {
                                &AppendExcludeEntry($path);
                                ++$destroyed_files->{$row->{physname}};
                            }
                        }
                    }
                    when (ACTION_BRANCH) {
                        # branches recorded in parent and child
                        # no git action required
                        my $link_info = File::Spec->catfile($gCfg{links}, $row->{info});

                        if ($row->{parentdata}) {
                            # set up bindings for the new branch
                            my $using_li = (-f $link_info);
                            my $p = ($using_li ? $link_info : $path);
                            if (!copy($p, $link_file)) { # should create new file
                                warn "$warn_msg path `$p' link `$link_file' copy $!";
                            } else {
                                unlink $path; # decrement any link count
                                link $link_file, $path; # add $path as the new link
                                @{$git_image->{$row->{physname}}} = ("$path");
                            }
                            # shouldn't need to 'git add', it's a file with the same contents

                            # remove bindings for the old one
                            my $path_re = qr/^\Q$path\E$/;
                            @{$git_image->{$row->{info}}} = grep {!/$path_re/} @{$git_image->{$row->{info}}};
                            if (scalar @{$git_image->{$row->{info}}} == 0) {
                                say "$warn_msg deleting git image $row->{info}" if $gCfg{debug};
                                delete $git_image->{$row->{info}};
                            }

                            # remove the path from excludes, and add it again if needed
                            &RewriteExcludes($path);
                            if ($using_li && $destroyed_files->{$row->{info}}) {
                                $destroyed_files->{$row->{physname}} = 1;
                                &AppendExcludeEntry($path);
                                if ($destroyed_files->{$row->{info}} >= 2) {
                                    --$destroyed_files->{$row->{info}};
                                }
                            } elsif (!$using_li) {
                                my $pathhash = $repo->logrun('hash-object' => '--', $path);
                                if ($gCfg{destroyedHash} eq $pathhash) {
                                    $destroyed_files->{$row->{physname}} = 1;
                                    &AppendExcludeEntry($path);
                                }
                            }
                        } elsif (! -f $link_file) {
                            # for some reason, the parent info is missing
                            # no parent info to link, just copy the link file
                            if (!copy($link_info, $link_file)) { # should create new file
                                warn "$warn_msg info `$link_info' link `$link_file' copy $!";
                            }
                            if ($destroyed_files->{$row->{info}}) {
                                $destroyed_files->{$row->{physname}} = 1;
                            }
                        }
                    }
                    when (ACTION_PIN) {
                        my $is_destroyed;
                        my $wrote_destroyed = 0;

                        if (defined $row->{info}) {
                            # this is an unpin
                            my $pin_name = $row->{physname} . $row->{info}; # The old pin version
                            $wrote_destroyed = &HandlePin($pin_name, $row->{physname}, $row->{physname},
                                                          "$warn_msg unpin", undef,
                                                          $link_file, $git_image, $path, $repo);
                        } else {
                            # this is a pin
                            # There's not a really good way to do this, since
                            # git doesn't suport this, nor do most Linux filesystems.
                            # Find the old version and copy it over...
                            my $pin_name = $row->{physname} . $row->{version};
                            $link_file .= $row->{version};
                            $wrote_destroyed = &HandlePin($row->{physname}, $pin_name, $row->{physname},
                                                          "$warn_msg pin", $row->{version},
                                                          $link_file, $git_image, $path, $repo);
                        }

                        unlink $path if -f $path; # get rid of pinned/unpinned file
                        link $link_file, $path;
                        if (!$wrote_destroyed) {
                            $repo->logrun(add => '--',  $path);
                        }
                    }
                    when (ACTION_LABEL) {
                        &DeferLabel($row, $repo);
                    }
                }
            }
        }
    };

    if ($@) {
        say "An error ($@) occurred";
        say "git_image: " . Dumper(\%git_image);
        say "row: " . Dumper($row);
        say "destroyed_files: " . Dumper($destroyed_files);
        die "can't finish reading actions";
    }

}

sub HandlePin {
    my($oldname, $newname, $physname, $msg, $version, $link_file, $git_image, $path, $repo) = @_;
    my $wrote_destroyed = 0;
    my $is_destroyed = 0;

    # only need to do this for pin
    if ($newname ne $physname) {
        my $efile = &ExportVssPhysFile($physname, $version, \$is_destroyed);
        if (defined $efile && ! -f $link_file) {
            if (!copy($efile, $link_file)) {
                warn "$msg export `$efile' path `$link_file' copy $!";
            } else {
                $wrote_destroyed = 1 if $is_destroyed;
            }
        } elsif (-f $link_file) {
            my $pathhash = $repo->logrun('hash-object' => '--', $link_file);
            $is_destroyed = ($pathhash eq $gCfg{destroyedHash});
        }
    }

    if (defined $git_image->{$newname}) {
        push @{$git_image->{$newname}}, $path;
    } else {
        @{$git_image->{$newname}} = ("$path");
    }
    # shouldn't need to 'git add', it's a file with the same contents

    # remove bindings for the old one
    my $path_re = qr/^\Q$path\E$/;
    @{$git_image->{$oldname}} = grep {!/$path_re/} @{$git_image->{$oldname}};
    if (scalar @{$git_image->{$oldname}} == 0) {
        say "$msg deleting git image $oldname" if $gCfg{debug};
        delete $git_image->{$oldname};
    }

    # remove the path from excludes, and add it again if needed
    my $id2;
    if ($id2 = (defined $destroyed_files->{$oldname})) {
        if ($destroyed_files->{$oldname} <= 1) {
            delete $destroyed_files->{$oldname};
        } else {
            --$destroyed_files->{$oldname};
        }
    }
    &RewriteExcludes($path);
    if ($wrote_destroyed || $is_destroyed || $id2) {
        $destroyed_files->{$newname} = 1;
        &AppendExcludeEntry($path);
    }

    return ($wrote_destroyed || $is_destroyed || $id2);
}

sub invalid_branch_name {
    my($dlabel) = @_;

    return (!defined $dlabel || $dlabel eq '' || $dlabel =~ $master_re);
}

# create a valid ref name for labeling
sub get_valid_ref_name {
    my($dlabel, $timestamp) = @_;

    # Got this regex from Stack Overflow
    # <http://stackoverflow.com/questions/12093748/how-do-i-check-for-valid-git-branch-names>
    # by Brendan Byrd <http://stackoverflow.com/users/968218/brendan-byrd> his answer is
    # here <http://stackoverflow.com/a/16857774/425738>.
    # Neither Stack Overflow nor Brendan Byrd endorses me or my use of their work.
    # SO is CC BY-SA 3.0 <http://creativecommons.org/licenses/by-sa/3.0/>
    # at the time of this writing.
    my $valid_ref_name = qr%
   ^
   (?!
      # begins with
      /|                # (from #6)   cannot begin with /
      # contains
      .*(?:
         [/.]\.|        # (from #1,3) cannot contain /. or ..
         //|            # (from #6)   cannot contain multiple consecutive slashes
         @\{|           # (from #8)   cannot contain a sequence @{
         \\             # (from #9)   cannot contain a \
      )
   )
                        # (from #2)   (waiving this rule; too strict)
   [^\040\177 ~^:?*[]+  # (from #4-5) valid character rules

   # ends with
   (?<!\.lock)          # (from #1)   cannot end with .lock
   (?<![/.])            # (from #6-7) cannot end with / or .
   $
%x;

    my $tagname;

    if (invalid_branch_name($dlabel)) {
        $dlabel = "@{[PROGNAME]}-$timestamp"; # better than nothing, I suppose
        goto GENSYM;
    } else {
        $tagname = $dlabel;
    }

    if (defined $label_map->{$dlabel}) {
        $tagname = $label_map->{$dlabel};
        goto DONE;
    }

    # hack $tagname until it works
    if ($tagname =~ m/${valid_ref_name}/) {
        goto DONE;
    }

    # remove any leading forward slash
    if ($tagname =~ m:^/(.*):) {
        $tagname = $1;
    }

    if ($tagname =~ m/${valid_ref_name}/) {
        goto DONE;
    }

    # remove any invalid sequences
    $tagname =~ s:([/.]\.|//|@\{|\\):_:g;

    if ($tagname =~ m/${valid_ref_name}/) {
        goto DONE;
    }

    # remove any invalid characters
    $tagname =~ s/[\040\177 ~^:?*[]/_/g;

    if ($tagname =~ m/${valid_ref_name}/) {
        goto DONE;
    }

    # remove any invalid endings
    $tagname =~ s:(\.lock|[/.])$:_:;

    # I really hope it's done here.
    if ($tagname =~ m/${valid_ref_name}/) {
        goto DONE;
    }

    # Give up, gensym
  GENSYM:
    my $ug = new Data::UUID;
    my $uuid = $ug->create_from_name_str(VSS2SVN2GIT_NS, $dlabel);
    $tagname = "@{[PROGNAME]}_" . $uuid;

  DONE:

    return $tagname;
}

# commit the changeset
sub GitCommit {
    my($repo, $comment, $username, $timestamp) = @_;

    my $map = $author_map->{$username};

    $repo->logrun( commit => '-a', '--allow-empty-message', '--no-edit', '-m',  $comment,
                {
                    env => {
                        GIT_AUTHOR_NAME => $map->{name},
                        GIT_AUTHOR_EMAIL => $map->{email},
                        GIT_AUTHOR_DATE => POSIX::strftime(ISO8601_FMT, localtime($timestamp)),
                    }
                });
}

# defer labeling until git master is complete
sub DeferLabel {
    my($row, $repo) = @_;

    my @pa_ary;
    foreach my $param (@physical_action_params) {
        push @pa_ary, keys %$param;
    }
    my $pa_params_sql = join q{,}, @pa_ary;

    # Copy it to the label table and remove it from the schedule
    my $sth = $gCfg{dbh}->prepare_cached("INSERT INTO PhysicalActionLabel "
                                         . "SELECT NULL AS schedule_id, action_id, $pa_params_sql "
                                         . "FROM PhysicalActionSchedule "
                                         . "WHERE schedule_id = ?",
                                         { dbi_dummy => __FILE__.__LINE__ });
    $sth->execute($row->{schedule_id});
    my $sid = $gCfg{dbh}->last_insert_id("","","","");
    $sth->finish();
    $sth = $gCfg{dbh}->prepare_cached('DELETE FROM PhysicalActionSchedule WHERE schedule_id = ?',
                                      { dbi_dummy => __FILE__.__LINE__ });
    $sth->execute($row->{schedule_id});
    $sth->finish();

    # bookmark HEAD and associate it with the label
    my $head_id = $repo->logrun('rev-parse' => 'HEAD');
    my $giti = nfreeze \%git_image;
    $sth = $gCfg{dbh}->prepare_cached('INSERT INTO LabelBookmark (label_id, schedule_id, head_id, git_image) '
                                      .'VALUES (NULL, ?, ?, ?)',
                                      { dbi_dummy => __FILE__.__LINE__ });
    $sth->execute($sid, $head_id, $giti);
    $sth->finish();
}

# create or checkout a branch for a label and add files to it from master
sub GitLabel {
    my($row, $repo, $head_id, $paths) = @_;
    my $sth = $gCfg{dbh}->prepare_cached('SELECT label FROM PhysLabel WHERE action_id = ?',
                                         { dbi_dummy => __FILE__.__LINE__ });
    $sth->execute($row->{action_id});
    ($row->{label}) = $sth->fetchrow_array();
    $sth->finish();

    my $tagname = get_valid_ref_name($row->{label}, $row->{timestamp});

    # copy each path into the label
    foreach my $path (@$paths) {
        # "git checkout <branch>" is hampered by absolute paths in this case
        # so we just strip off the repo dir
        my @tagnamedir = File::Spec->splitdir($path);
        my @repodir = File::Spec->splitdir($gCfg{repo});

        @tagnamedir = @tagnamedir[(scalar @repodir)..$#tagnamedir];
        my $tmppath;
        if ($row->{itemtype} == VSS_FILE) {
            $tmppath = File::Spec->catfile(@tagnamedir);
        } else {
            $tmppath = File::Spec->catdir(@tagnamedir);
        }

        $repo->logrun(checkout => '-q', $head_id, '--',  $tmppath);
    }
}

# handle different kinds of moves
sub DoMoveProject {
    my($repo, $path, $newpath, $git_image, $newtest) = @_;
    my $imatch = ($path =~ /^\Q$newpath\E$/i);

    if ($newtest ? ((! -d $newpath) || $imatch) : (-d $path)) {
        if ($imatch) {
            my $tmp_mv = File::Spec->catdir(dirname($path), MOVE_TMP_FILE);
            $repo->logrun(mv =>  $path,  $tmp_mv);
            $repo->logrun(mv =>  $tmp_mv,  $newpath);
        } else {
            $repo->logrun(mv =>  $path,  $newpath);
        }
        # N.B. inode should _not_ have changed during move
        &MoveProject($path, $newpath, $git_image);
    }
}

# remove the directory keep file if there is one
sub RemoveKeep {
    my($repo, $parentpath) = @_;

    my $keep = File::Spec->catfile($parentpath, KEEP_FILE);

    $repo->logrun(rm => '-f', '-q', '--',  $keep) if -f $keep;
}

sub LastDeleteTime {
    my($physname, $timestamp) = @_;
    my $tmp_sth = $gCfg{dbh}->prepare_cached("SELECT action_id "
                                              . "FROM PhysicalAction "
                                              . "WHERE physname = ? AND actiontype = '@{[ACTION_DELETE]}' "
                                              . "AND timestamp =  "
                                              . "(SELECT MAX(timestamp) "
                                              . " FROM PhysicalAction "
                                              . " WHERE physname = ? AND actiontype = '@{[ACTION_DELETE]}' "
                                             . " AND timestamp < ?)",
                                             { dbi_dummy => __FILE__.__LINE__ });
    $tmp_sth->execute($physname, $physname, $timestamp);
    my ($action_id_del) = $tmp_sth->fetchrow_array();
    $tmp_sth->finish();
    return $action_id_del;
}

# handle the recover
sub GitRecover {
    my($repo, $row, $path, $git_image) = @_;

    my $is_destroyed = 0;
    my $tmp_sth = $gCfg{dbh}->prepare_cached("SELECT action_id "
                                             . "FROM PhysicalAction "
                                             . "WHERE physname = ? AND actiontype = '@{[ACTION_DESTROY]}' "
                                             . "LIMIT 1",
                                             { dbi_dummy => __FILE__.__LINE__ });
    $tmp_sth->execute($row->{physname});
    my ($action_id) = $tmp_sth->fetchrow_array();
    $tmp_sth->finish();
    my $action_id_del = &LastDeleteTime($row->{physname}, $row->{timestamp});

    if (! -e $path) {
        for ($row->{itemtype}) {
            when (VSS_PROJECT) {
                if (!$action_id) {
                    if (defined $action_id_del) {
                        my $delete_loc = File::Spec->catdir($gCfg{deleted}, $action_id_del);
                        if (!move($delete_loc, $path)) {
                            warn "GitRecover: move project delete loc: `$delete_loc' path: `$path' $!";
                        } else {
                            $repo->logrun(add => '--',  $path);
                            $git_image->{$row->{physname}} = $path;
                        }
                    }
                } else {
                    # XXX don't know what to do here
                    # probably should do nothing anyway
                }
            }
            when (VSS_FILE) {
                my $link_file = File::Spec->catfile($gCfg{links}, $row->{physname});
                if (!$action_id) {
                    if (defined $action_id_del) {
                        my $delete_loc = File::Spec->catfile($gCfg{deleted}, $action_id_del);
                        if (!move($delete_loc, $path)) {
                            warn "GitRecover: move file delete loc: `$delete_loc' path: `$path' $!";
                        } else {
                            @{$git_image->{$row->{physname}}} = ("$path");
                        }
                    }
                } else {
                    if (-f $link_file) {
                        # we have a backup from history (we were BRANCHed)
                        link $link_file, $path; # add $path as the new link
                    } else {
                        # no history backup, fake it
                        if (!copy($gCfg{destroyedFile}, $link_file)) {  # touch the file
                            warn "GitRecover: copy destroyed file path `$link_file' copy $!";
                        } else {
                            $is_destroyed = 1;
                            link $link_file, $path;
                        }
                    }
                    @{$git_image->{$row->{physname}}} = ("$path");
                }
                if (!$is_destroyed) {
                    $repo->logrun(add => '--',  $path);
                    &RemoveKeep($repo, dirname($path));
                } else {
                    $destroyed_files->{$path} = 1;
                    &AppendExcludeEntry($path);
                }
            }
        }
    }
}

sub GitRm {
    my($repo, $parentpath, $path, $itemtype, $actiontype, $action_id) = @_;

    # add back the keep file before 'git rm', so we don't have to reset
    # inode bookkeeping
    my $keepfile = File::Spec->catfile($parentpath, KEEP_FILE);
    if (!copy($gCfg{keepFile}, $keepfile)) {
        warn "GitRm: path `$keepfile' copy $!";
    }

    if ($actiontype eq ACTION_DELETE) {
        # these can be restored, so lets move them to a safe location
        my $delete_loc;
        if ($itemtype == VSS_PROJECT) {
            $delete_loc = File::Spec->catdir($gCfg{deleted}, $action_id);
        } else {
            $delete_loc = File::Spec->catfile($gCfg{deleted}, $action_id);
        }
        if (!move($path, $delete_loc)) {
            warn "GitRm: move path: `$path' delete loc: `$delete_loc' $!";
        }
    }

    $repo->logrun(rm => ($itemtype == VSS_PROJECT ? '-rf' : '-f'), '-q', '--',  $path);

    # count the files in parentpath to see if the keep file should be added
    opendir(my $DIR, $parentpath);
    my $parentpath_dir_files = () = readdir $DIR;
    closedir $DIR;

    if ($parentpath_dir_files == 3) {
        $repo->logrun(add => '--',  $keepfile);
    } else {
        unlink $keepfile;
    }
}

sub SearchForPath {
    my($physname, $git_image) = @_;
    my $link_file = File::Spec->catfile($gCfg{links}, $physname);
    my $path;

    if (defined $git_image->{$physname}) {
        $path = @{$git_image->{$physname}}[0];
    } elsif (-f $link_file) {
        $path = $link_file
    }

    return $path;
}

# From <http://support.microsoft.com/KB/171350>
sub PhyToNum {
    my($physname) = @_;
    use bigint;

    my $lFileNum = 0;
    my @pchars = split("", $physname);
    my $i;

    for ( $i = $#pchars; $i >= 0; --$i ) {
        $lFileNum *= 26;  # Multiply by the appropriate power of 26
        $lFileNum += (ord($pchars[$i]) - ord('A')); # Convert the value
    }
    return ($lFileNum);
}

# rewrite the excludes without this path
sub MoveExcludes {
    my($oldpath, $newpath) = @_;
    my $sep = "/"; # XXX not platform independent
    $oldpath =~ s/$repo_re/\//;
    $newpath =~ s/$repo_re/\//;
    my $oldpath_re = qr/^\Q${oldpath}${sep}\E(.*)$/;

    open FILE, "<$gCfg{exclude}" or die "Could not open $gCfg{exclude}: $!";
    my @lines = <FILE> ;
    close FILE;

    s/$oldpath_re/${newpath}${sep}$1/ for @lines;

    # clean up extra paths, just in case
    my %set = map { $_ => 1 } @lines;
    @lines = keys %set;

    open FILE, ">$gCfg{exclude}";
    say FILE @lines;
    close FILE;
}

# rewrite the excludes without this path
sub RewriteExcludes {
    my($path, $project) = @_;

    open FILE, "<$gCfg{exclude}" or die "Could not open $gCfg{exclude}: $!";
    my @lines = <FILE> ;
    close FILE;

    $path =~ s/$repo_re/\//;
    my $path_re = (defined $project) ? qr/^\Q$path\E/ : qr/^\Q$path\E$/;

    @lines = grep {!/$path_re/} @lines;

    # clean up extra paths, just in case
    my %set = map { $_ => 1 } @lines;
    @lines = keys %set;

    open FILE, ">$gCfg{exclude}";
    say FILE @lines;
    close FILE;
}

# add an entry to the exclude file
sub AppendExcludeEntry {
    my($path) = @_;

    open FILE, ">>$gCfg{exclude}";
    $path =~ s/$repo_re/\//;
    say FILE "$path";
    close FILE;
}

__END__

=head1 NAME

vss2svn2git.pl -- Import a Visual SourceSafe database into a git repository

=head1 SYNOPSIS

vss2svn2git.pl --vssdir F<directory> --author_info F<file> [options]

  Required:
    --vssdir F<directory>      VSS database
    --author_info F<file>      mappings for VSS usernames to git authors

  Options:
    --ssphys F<file>           Path to ssphys program
    --tempdir F<directory>     vss2svn2git work directory
    --repo F<directory>        git repository directory
    --revtimerange <int>       maximum commit time
    --encoding <encoding>      specify VSS encoding
    --resume                   resume failed or aborted run
    --task <task>              specify task to resume
    --verbose                  print more info during processing
    --debug                    print debugging output
    --timing                   print timing info

=over 8

=item B<--ssphys>

Specify a path to the ssphys program.  It reads the VSS database.

=item B<--tempdir>

Work directory to use during conversion.  Defaults to C<_vss2svn2git>.
Must be on the same filesystem as I<--repo>.

=item B<--repo>

The git directory to use during conversion.  Defaults to C<repo>.
Must be on the same filesystem as I<--tempdir>.

=item B<--revtimerange>

The maximum time difference in seconds that may be spanned by a
git commit.  Defaults to 3600 s.

=item B<--encoding>

Specify the VSS encoding to use.  Defaults to C<windows-1252>.

=item B<--resume>

Resume a failed or aborted previous run.

=item B<--task>

Specify the task to resume.

=item B<--verbose>

Print more information to the standard output during conversion.

=item B<--debug>

Print more information to the standard output during conversion.

=item B<--timing>

Print timing information.

=back

=head1 DESCRIPTION

Migrate the Visual SourceSafe database given by I<--vssdir> using the
VSS/git author information given by I<--author_info>.

=cut
