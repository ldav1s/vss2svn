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
use Storable qw(dclone);

use lib '.';
use POSIX;
use Git;
use Data::Dumper;

require Encode;

use constant {
    TASK_INIT => 'INIT',
    TASK_LOADVSSNAMES => 'LOADVSSNAMES',
    TASK_FINDDBFILES => 'FINDDBFILES',
    TASK_GETPHYSHIST => 'GETPHYSHIST',
    TASK_REMOVETMPCHECKIN => 'REMOVETMPCHECKIN',
    TASK_FIXUPPARENT => 'FIXUPPARENT',
    TASK_TESTGITAUTHORINFO => 'TESTGITAUTHORINFO',
    TASK_GITREAD => 'GITREAD',
    TASK_DONE => 'DONE',
};

use constant {
    TEMPDIR => '_vss2svn',
    REPO => 'repo',
    REVTIMERANGE => 3600,
    ENCODING => 'windows-1252',
    VSS_PROJECT => 1,
    VSS_FILE => 2,
    BRANCH_TMP_FILE => '.vss2svn2gitbranchtmp',
    KEEP_FILE => '.vss2svn2gitkeep',
    VSS2SVN2GIT_NS => 'ns:vss2svn2git',
    PROGNAME => 'vss2svn2git',
    PROGNAME_URL => 'https://github.com/ldav1s/vss2svn',
    VSSDB_ROOT => 'AAAAAAAA',
    ISO8601_FMT => '%Y-%m-%dT%H:%M:%S',
    MINMAX_TIME_FMT => '%Y-%m-%d',
    PA_PRIORITY_MAX => 5,
    # This is arbitrary, tried to keep it fairly small
    PAIR_INSERT_VAL => 256,
    # This is arbitrary, tried to keep it fairly small
    PHYSICAL_FILES_LIMIT => 512,
    # This is arbitrary, tried to keep it fairly small
    PA_PARAMS_LIMIT => 16,
    # This is arbitrary, tried to keep it really small
    TIMESTAMP_DELTA => 4,
};

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

our(%gCfg, %gSth, %gErr, $gSysOut);

our $VERSION = '0.11.0-nightly.$LastChangedRevision$';
$VERSION =~ s/\$.*?(\d+).*\$/$1/; # get only the number out of the svn revision

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
my $label_map = ();

# The author map maps VSS author information to git author information
my $author_map = ();

# The main VSS activity is put into git master, and labels into their own branch
my $master_re = qr/master/;

# store a hash of actions to take; allows restarting in case of failed
# migration
my @joblist =
    (
     {
         task    => TASK_INIT,
         handler => sub{ 1; },
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
     # Initialize the git repo and a few in memory structures
     {
         task => TASK_GITREAD,
         handler => \&GitReadImage,
     },
     # done state
     {
         task    => TASK_DONE,
         handler => sub { 1; },
     }
    );

# Data for PhyicalAction table
my @physical_action_params = (
{        'physname' =>    'VARCHAR' },
{        'version' =>     'INTEGER'},
{        'parentphys' =>  'VARCHAR'},
{        'actiontype' =>  'VARCHAR'},
{        'itemname' =>    'VARCHAR'},
{        'itemtype' =>    'INTEGER'},
{        'timestamp' =>   'INTEGER'},
{        'author' =>      'VARCHAR'},
{        'is_binary' =>   'INTEGER'},
{        'info' =>        'VARCHAR'},
{        'priority' =>    'INTEGER'},
{        'parentdata' =>  'INTEGER'},
{        'label' =>       'VARCHAR'},
{        'comment' =>     'TEXT'},
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


    my $info;
    my $taskmap = {};
    my $i = 0;

    foreach my $e (@joblist) {
        $taskmap->{$e->{task}} = $i++;
    }

    die "FATAL ERROR: Unknown task '$gCfg{task}'\n"
        unless defined $taskmap->{$gCfg{task}};

    for ($i = $taskmap->{$gCfg{task}}; $i < (scalar @joblist)-1; ++$i) {
        $info = $joblist[$i];

        print "TASK: $gCfg{task}: "
            . POSIX::strftime(ISO8601_FMT . "\n", localtime) . "\n";
        push @{ $gCfg{tasks} }, $gCfg{task};

        if ($gCfg{prompt}) {
            print "Press ENTER to continue...\n";
            my $temp = <STDIN>;
            die if $temp =~ m/^quit/i;
        }


        &{ $info->{handler} };
        &SetSystemTask( $joblist[$i+1]->{task} );
    }

}  #  End RunConversion

###############################################################################
#  LoadVssNames
###############################################################################
sub LoadVssNames {
    my @cmd = ('info', "-e$gCfg{encoding}",
               File::Spec->catdir($gCfg{vssdatadir}, 'names.dat'));
    &DoSsCmd(@cmd);

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

    $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;

    eval {
        my $vssdb_cnt = 0;
        my @dirs = ($gCfg{vssdatadir});
        my $start_depth = $gCfg{vssdatadir} =~ tr[/][];
        my $vssfile_depth = $start_depth + 1;
        my @phys_list = ();

        find({
            preprocess => sub {
                my $depth = $File::Find::dir =~ tr[/][];
                return sort grep { -d $_ && $_ =~ m:^[a-z]{1}$:i } @_ if $depth < $vssfile_depth;
                return sort grep { -f $_ && $_ =~ m:^[a-z]{8}$:i } @_ if $depth == $vssfile_depth;
            },
            wanted => sub {
                my $depth = $File::Find::dir =~ tr[/][];
                return if $depth != $vssfile_depth;
                push @phys_list, uc($_), $File::Find::name;
                ++$vssdb_cnt;
                if (scalar @phys_list >= PAIR_INSERT_VAL) {
                    &LoadUpPhysical(\@phys_list);
                    @phys_list = ();
                }
            },
             }, @dirs);

        if (scalar @phys_list > 0) {
            &LoadUpPhysical(\@phys_list);
            @phys_list = ();
        }
        print "Found $vssdb_cnt VSS database files at '$gCfg{vssdatadir}'\n" if $gCfg{verbose};
    };

    if ($@) {
        warn "Transaction aborted because $@";
        eval { $gCfg{dbh}->rollback };
        die "Failed to load physical table";
    } else {
        $gCfg{dbh}->commit;
    }

    1;
}  #  End FindPhysDbFiles

sub LoadUpPhysical {
    my($phys_list) = @_;

    my $val_clause = join q{,}, ('(?, ?)') x ((scalar @{$phys_list})/2);
    my $sth = $gCfg{dbh}->prepare("INSERT INTO Physical (physname, datapath) VALUES $val_clause");
    $sth->execute(@{$phys_list});
}

###############################################################################
#  GetPhysVssHistory
###############################################################################
sub GetPhysVssHistory {

    my $physname = '';
    my $limcount = 0;

    # Break up inserts into multiple transactions
    # Most files have one insert only (and most one set of VALUES only)!
    my $sth = $gCfg{dbh}->prepare("SELECT * FROM Physical "
                               . "WHERE physname > ? "
                               . "ORDER BY physname LIMIT @{[PHYSICAL_FILES_LIMIT]}");
    do {
        $sth->execute($physname);

        $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
        $limcount = 0;
        eval {
            my $row;
            while (defined($row = $sth->fetchrow_hashref() )) {
                $physname = $row->{physname};
                &GetVssPhysInfo($row->{datapath}, $physname);
                ++$limcount;
            }
        };
        if ($@) {
            warn "Transaction aborted because $@";
            eval { $gCfg{dbh}->rollback };
            die "Failed to load VSS items for `$physname'";
        } else {
            $gCfg{dbh}->commit;
        }
    } while ($limcount == PHYSICAL_FILES_LIMIT);

    1;
}  #  End GetPhysVssHistory

###############################################################################
#  GetVssPhysInfo
###############################################################################
sub GetVssPhysInfo {
    my($datapath, $physname) = @_;

    print "datapath: \"$datapath\"\n" if $gCfg{debug};
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

    for ($type+0) {
        when (VSS_PROJECT) {
            $parentphys = $xmldoc->findvalue('File/ItemInfo/ParentPhys');
        }
        when (VSS_FILE) { $parentphys = undef; }
        default {
            &ThrowWarning("Can't handle file '$physname'; not a project or file\n");
            return;
        }
    }

    my @versions = $xmldoc->findnodes('File/Version');

    if (scalar @versions > 0) {
        &GetVssItemVersions($physname, $parentphys, \@versions, $type, $binary);
    }

}  #  End GetVssPhysInfo

###############################################################################
#  GetVssItemVersions
###############################################################################
sub GetVssItemVersions {
    my($physname, $parentphys, $versions, $ii_type, $ii_binary) = @_;

    my($parentdata, $version, $vernum, $actionid, $actiontype,
       $tphysname, $itemname, $itemtype, $parent, $user, $timestamp, $comment,
       $is_binary, $info, $priority, $label, $cachename);

    my @pa_list = ();
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
        Labeled => {type => VSS_FILE, action => ACTION_LABEL},
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
        $is_binary = 0;
        $info = undef;
        $parentdata = 0;
        $priority = PA_PRIORITY_MAX;
        $label = undef;

        if ($version->exists('Comment')) {
            $comment = $version->findvalue('Comment') || undef;
        }

        # In case of Label the itemtype is the type of the item currently
        # under investigation
        if ($actiontype eq ACTION_LABEL) {
            $itemtype = $ii_type;
        }
        # we can have label actions and labels attached to versions
        if ($version->exists('Action/Label')) {
            $label = $version->findvalue('Action/Label');
            my $lcom = $version->findvalue('Action/LabelComment');
            # append the label comment to a possible version comment
            if (defined $lcom && $lcom ne '') {
                if (defined $comment) {
                    print "Merging LabelComment and Comment for "
                        . "'$tphysname;$vernum'\n"; # if $gCfg{verbose};
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

        if ($itemtype == VSS_FILE) {
            $is_binary = $ii_binary;
        }

        for ($actiontype) {
            when (ACTION_RENAME) {
                # if a rename, we store the new name in the action's 'info' field
                $info = &GetItemName($version->findvalue('Action/NewSSName'),
                                     $version->findvalue('Action/NewSSName/@offset'),
                                     $namelookup);
            }
            when (ACTION_BRANCH) {
                $info = $version->findvalue('Action/Parent');
            }
            when (ACTION_MOVE_TO) {
                $info = $version->findvalue('Action/DestPath');
                $info =~ s/^..(.*)$/$1/;
            }
            when (ACTION_MOVE_FROM) {
                $info = $version->findvalue('Action/SrcPath');
                $info =~ s/^..(.*)$/$1/;
            }
        }



        # since there is no corresponding client action for PIN, we need to
        # enter the concrete version number here manually
        # In a share action the pinnedToVersion attribute can also be set
        $vernum = $version->findvalue('Action/PinnedToVersion') if ($version->exists('Action/PinnedToVersion'));

        # for unpin actions also remeber the unpinned version
        $info = $version->findvalue('Action/UnpinnedFromVersion') if ($version->exists('Action/UnpinnedFromVersion'));

        for ($actiontype) {
            when (ACTION_ADD) { $priority -= 4; }
            when (ACTION_SHARE) { $priority -= 3; }
            when (ACTION_PIN) { $priority -= 3; }
            when (ACTION_BRANCH) { $priority -= 2; }
        }


        push @pa_list, $tphysname, $vernum, $parentphys, $actiontype, $itemname,
        $itemtype, $timestamp, $user, $is_binary, $info, $priority,
        $parentdata, $label, $comment;

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
            push @pa_list, $tphysname, $vernum, $parentphys, ACTION_LABEL, $itemname,
            $itemtype, $timestamp, $user, $is_binary, $info, PA_PRIORITY_MAX,
            $parentdata, $vlabel, $labelComment;
        }

        if (scalar @pa_list >= PA_PARAMS_LIMIT*(scalar @physical_action_params)) {
            &LoadUpPhysActionInfo(\@pa_list);
            @pa_list = ();
        }
    }

    if (scalar @pa_list > 0) {
        &LoadUpPhysActionInfo(\@pa_list);
        @pa_list = ();
    }

}  #  End GetVssItemVersions

sub LoadUpPhysActionInfo {
    my($pa_list) = @_;

    my @pa_ary;
    foreach my $param (@physical_action_params) {
        push @pa_ary, keys %$param;
    }
    my $pa_params_sql = join q{,}, @pa_ary;
    my $val_params = join q{,}, ('?') x (scalar @pa_ary);
    my $val_clause = join q{,}, ("(NULL, $val_params)") x ((scalar @{$pa_list})/(scalar @pa_ary));
    my $sql = "INSERT INTO PhysicalAction (action_id, $pa_params_sql) VALUES $val_clause";

    my $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute(@{$pa_list});
}

###############################################################################
#  GetItemName
###############################################################################
sub GetItemName {
    my($itemname, $offset, $namelookup) = @_;

    if (defined $offset
        && defined $namelookup->{$offset}
        && defined $namelookup->{$offset}->{name}) {
        my $newname = $namelookup->{$offset}->{name};
        print "Changing name of '$itemname' to '$newname' from "
            . "name cache\n" if $gCfg{debug};
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

    $sth = $gCfg{dbh}->prepare("SELECT DISTINCT author "
                               ."FROM PhysicalAction "
                               . "WHERE author NOT IN ($in_clause) "
                               . "ORDER BY author");
    $sth->execute(@amk);
    $rows = $sth->fetchall_arrayref( {} );

    foreach my $row (@$rows) {
        ++$err;
        print "Found unknown username `$row->{author}'.\n";
    }

    die "author file '$gCfg{author_info}' is incomplete." if $err;

    1;
}

###############################################################################
#  GitReadImage
###############################################################################
sub GitReadImage {
    # Read the physical actions, and perform them on the repository

    my($sth, $tth, $rows);
    my ($last_time);

    &TimestampLimits;

    my $repo = Git->repository(Directory => "$gCfg{repo}");

    $last_time = $gCfg{mintime};
    $sth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalActionSchedule ORDER BY schedule_id');

    $tth = $gCfg{dbh}->prepare('SELECT MIN(timestamp) FROM PhysicalAction WHERE timestamp > ?');

    my $dump_cnt = 0;
    while ($last_time < $gCfg{maxtime}) {
        my ($username, $comment);

        print "timestamp: $last_time\n";

        &SchedulePhysicalActions($last_time);

        $sth->execute();
        $rows = $sth->fetchall_arrayref( {} );

        undef $username;

        # It's not an error to have 0 scheduled rows

        foreach my $row (@$rows) {
            $last_time = $row->{timestamp};
            $username = $row->{author};
            $comment = $row->{comment};

            my ($path, $parentpath);

#            if ($dump_cnt % 100 == 0) {
#                print "git_image: " . Dumper(\%git_image) . "\n";
#                if ($dump_cnt == 100) {
#                    exit(0);
#                }
#            }
            ++$dump_cnt;

            if (defined $row->{parentphys}) {
                print "parentphys: " . $row->{parentphys} .
                    " physname: " . $row->{physname} .
                    " timestamp: " .  $row->{timestamp} . "\n";
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

            &UpdateGitRepository($row, $parentpath, $path, \%git_image, 0, $repo);
        }

        if (defined $username) {
            &GitCommit($repo, $comment, $username, $last_time);
            ++$gCfg{commit};
        }

        # get the next changeset
        if ($last_time < $gCfg{maxtime}) {
            ++$gCfg{changeset};
            $tth->execute($last_time);
            $last_time = $tth->fetchall_arrayref()->[0][0];

        }

        # Retire old data
        $gCfg{dbh}->do("INSERT INTO PhysicalActionRetired "
                       ."SELECT NULL AS retired_id, "
                       . "$gCfg{commit} AS commit_id, $gCfg{changeset} AS changeset, * FROM PhysicalActionSchedule "
                       . "ORDER BY schedule_id");
        $gCfg{dbh}->do('DELETE FROM PhysicalActionSchedule');
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
    foreach my $key (keys %git_image) {
        if (ref($git_image{$key})) {
            my $ary = $git_image{$key};
            my $base = shift @$ary;
            $base =~ s/^\Q$gCfg{repo}\E.//; # XXX not portable

            if (scalar @$ary > 0) {
                my @basedir = File::Spec->splitdir($base);

                unshift @basedir, File::Spec->updir();
                unshift @basedir, '$GIT_DIR';

                my $basepath = File::Spec->catfile(@basedir);

                push @shares, "#";
                push @shares, "# $base";
                push @shares, "#";

                # synthesize the hard link
                # XXX This could be a shell quoting nightmare...
                foreach my $e (@$ary) {
                    my @edir = File::Spec->splitdir($e);
                    unshift @edir, File::Spec->updir();
                    unshift @edir, '$GIT_DIR';

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

    # snap the links
    rmtree($gCfg{links});

    1;
}

###############################################################################
# RemoveTemporaryCheckIns
# remove temporary checkins that where create to detect MS VSS capabilities
###############################################################################
sub RemoveTemporaryCheckIns {
    my $sql = <<"EOSQL";
DELETE FROM PhysicalAction WHERE action_id IN
(SELECT action_id
 FROM PhysicalAction
 WHERE physname IN
 (SELECT physname
  FROM PhysicalAction
  WHERE actiontype = '@{[ACTION_ADD]}'
  AND itemtype = @{[VSS_FILE]}
  AND comment = 'Temporary file created by Visual Studio .NET to detect Microsoft Visual SourceSafe capabilities.'))
EOSQL

    $gCfg{dbh}->do($sql);

    1;
}

###############################################################################
# FixupParentActions
# Fixes up typical ACTION_ADD, ACTION_BRANCH missing comment data for parents in PhysicalAction
###############################################################################
sub FixupParentActions {
    my $sql = <<"EOSQL";
SELECT B.comment AS comment, A.action_id AS action_id
FROM (SELECT physname, action_id
      FROM PhysicalAction
      WHERE itemtype = ?
      AND parentdata != 0
      AND actiontype = '@{[ACTION_ADD]}') AS A
NATURAL JOIN (SELECT physname, comment
              FROM PhysicalAction
              WHERE itemtype = ?
              AND parentdata = 0
              AND actiontype = '@{[ACTION_ADD]}') AS B
EOSQL
    my $sth = $gCfg{dbh}->prepare($sql);
    my $tth = $gCfg{dbh}->prepare('UPDATE PhysicalAction '
                                  .'SET comment = ? '
                                  .'WHERE action_id = ? '
                                  .'AND comment IS NULL ');
    my $row;

    foreach my $type (VSS_PROJECT, VSS_FILE) {
        $sth->execute($type, $type);

        $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
        eval {
            while (defined($row = $sth->fetchrow_hashref() )) {
                $tth->execute($row->{comment}, $row->{action_id});
            }
        };

        if ($@) {
            warn "Transaction aborted because $@";
            eval { $gCfg{dbh}->rollback };
            die "Failed to fix up ADDs";
        } else {
            $gCfg{dbh}->commit;
        }
    }

    # timestamp seems to be earlier in child than parent
    # give each branch a little wiggle room timestamp-wise
    $sql = <<"EOSQL";
SELECT B.comment AS comment, A.action_id AS action_id, B.timestamp AS timestamp
FROM (SELECT physname, action_id
      FROM PhysicalAction
      WHERE itemtype = @{[VSS_FILE]}
      AND parentdata != 0
      AND actiontype = '@{[ACTION_BRANCH]}') AS A
INNER JOIN (SELECT physname, comment, timestamp
              FROM PhysicalAction
              WHERE itemtype = @{[VSS_FILE]}
              AND parentdata = 0
              AND actiontype = '@{[ACTION_BRANCH]}') AS B
USING (physname)
EOSQL
    $sth = $gCfg{dbh}->prepare($sql);
    $tth = $gCfg{dbh}->prepare("UPDATE PhysicalAction "
                               . "SET comment = ? "
                               . "WHERE action_id = ? "
                               . "AND comment IS NULL "
                               . "AND timestamp BETWEEN ? AND ?");

    $sth->execute();

    $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
    eval {
        while (defined($row = $sth->fetchrow_hashref() )) {
            $tth->execute($row->{comment}, $row->{action_id},
                          $row->{timestamp}-(TIMESTAMP_DELTA), $row->{timestamp}+(TIMESTAMP_DELTA));
        }
    };

    if ($@) {
        warn "Transaction aborted because $@";
        eval { $gCfg{dbh}->rollback };
        die "Failed to fix up BRANCHes";
    } else {
        $gCfg{dbh}->commit;
    }

    1;
}

###############################################################################
#  CheckForDestroy
###############################################################################
sub CheckForDestroy {
    my($exportdir, $physname, $version, $destroyonly) = @_;
    my($row, $physpath, $rowd);

    # physical file doesn't exist; it must have been destroyed earlier
    # search and see if it was DESTROYed first
    $row = $gCfg{dbh}->selectrow_arrayref("SELECT action_id FROM PhysicalAction "
                                          . "WHERE physname = ? AND "
                                          . "actiontype = '@{[ACTION_DESTROY]}'",
                                          undef, $physname);

    if (!$destroyonly) {
        $rowd = $gCfg{dbh}->selectrow_arrayref("SELECT action_id FROM PhysicalAction "
                                               . "WHERE physname = ? AND "
                                               . "actiontype = '@{[ACTION_DELETE]}'",
                                               undef, $physname);
    }

    if (!(defined $row && defined $row->[0]) && !(defined $rowd && defined $rowd->[0])) {
        # we have no idea if it was DESTROYed or DELETEd
        &ThrowWarning("Can't retrieve revisions from physical file "
                      . "'$physname'; it was possibly corrupted or was not in place before "
                      . "the last GETPHYSHIST task was run.");

        $physpath = "$exportdir/$physname.$version";
        if (! -e $physpath) {
            if (!copy("$gCfg{indeterminateFile}", $physpath)) {
                print "CheckForDestroy: indeterminate copy $!\n";
            }
        }
    } else {
        # It was DESTROYed or DELETEd
        $physpath = "$exportdir/$physname.$version";
        if (! -e $physpath) {
            if (defined $row && defined $row->[0]) {
                if (!copy("$gCfg{destroyedFile}", $physpath)) {
                    print "CheckForDestroy: destroyed copy $!\n";
                }
            } elsif (defined $rowd && defined $rowd->[0]) {
                if (!copy("$gCfg{deletedFile}", $physpath)) {
                    print "CheckForDestroy: deleted copy $!\n";
                }
            }
        }
    }
    return $physpath;
}

###############################################################################
#  ExportVssPhysFile
###############################################################################
sub ExportVssPhysFile {
    my($physname, $version) = @_;
    my($row, $physpath);

    $physname =~ m/^(..)/;

    my $exportdir = "$gCfg{vssdata}/$1";

    make_path($exportdir) if ! -e $exportdir;
    $row = $gCfg{dbh}->selectrow_arrayref("SELECT datapath FROM Physical WHERE physname = ?", undef, $physname);

    if (!(defined $row && defined $row->[0])) {
        if (! defined $version) {
            $version = 1;
        }
        $physpath = &CheckForDestroy($exportdir, $physname, $version, 1);
    } else {
        $physpath = $row->[0];
    }

    if (! -f $physpath) {
        # physical file doesn't exist; it must have been destroyed later since find was run
        &ThrowWarning("Can't retrieve revisions from VSS database file "
                      . "'$physpath'; it was destroyed after the last GETPHYSHIST task was run.");
        return undef;
    }

    # MergeParentData normally will merge two corresponding item and parent
    # actions. But if the actions are more appart than the maximum allowed
    # timespan, we will end up with an undefined version in an ADD action here
    # As a hot fix, we define the version to 1, which will also revert to the
    # alpha 1 version behavoir.
    if (! defined $version) {
        &ThrowWarning("'$physname': no version specified for retrieval");

        # fall through and try with version 1.
        $version = 1;
    }

    if (! -e "$exportdir/$physname.$version" ) {
        # get all versions we can find from the physical file
        my @cmd = ('get', '-b', "-v$version", '--force-overwrite',
                   "-e$gCfg{encoding}", $physpath,
                   File::Spec->catdir($exportdir, $physname));
        &DoSsCmd(@cmd);
        if (! -e "$exportdir/$physname.$version") {
            $physpath = &CheckForDestroy($exportdir, $physname, $version, 0);
        }
    }

    return $exportdir;
}  #  End ExportVssPhysFile

###############################################################################
#  ShowHeader
###############################################################################
sub ShowHeader {
    my $info = $gCfg{task} eq TASK_INIT ? 'BEGINNING CONVERSION...' :
        "RESUMING CONVERSION FROM TASK '$gCfg{task}' AT STEP $gCfg{step}...";
    my $starttime = ctime($^T);

    my $ssversion = &GetSsVersion();

    print <<"EOTXT";
======== VSS2SVN ========
$info
Start Time   : $starttime

VSS Dir      : $gCfg{vssdir}
Temp Dir     : $gCfg{tempdir}
git repo     : $gCfg{repo}
VSS Encoding : $gCfg{encoding}

VSS2SVN ver  : $VERSION
SSPHYS exe   : $gCfg{ssphys}
SSPHYS ver   : $ssversion
XML Parser   : $gCfg{xmlParser}
Task         : $gCfg{task}
Rev Time     : $gCfg{revtimerange}

EOTXT

    my @version = split '\.', $ssversion;
    # we need at least ssphys 0.22
    if ($version[0] == 0 && $version[1] < 22) {
        &ThrowError("The conversion needs at least ssphys version 0.22");
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

        my $hours = $secs / 3600;
        $secs -= ($hours * 3600);

        my $mins = $secs / 60;
        $secs -= ($mins * 60);

        $elapsed = sprintf("%2.2i:%2.2i:%2.2i", $hours, $mins, $secs);
    }

    my($actions, $discarded, $revisions, $mintime, $maxtime) = &GetStats();

    print <<"EOTXT";
Started at              : $starttime
Ended at                : $endtime
Elapsed time            : $elapsed (H:M:S)

VSS Actions read        : $actions
VSS Actions discarded   : $discarded
git commits converted   : $revisions
Date range (YYYY-MM-DD) : $mintime to $maxtime

EOTXT

}  #  End ShowSummary

###############################################################################
#  GetStats
###############################################################################
sub GetStats {
    my($actions, $discarded, $mintime, $maxtime);

    ($actions) = $gCfg{dbh}->selectrow_array('SELECT COUNT(*) FROM PhysicalActionRetired');
    ($discarded) = $gCfg{dbh}->selectrow_array('SELECT COUNT(*) FROM PhysicalActionDiscarded');

    $mintime = $gCfg{mintime};
    $maxtime = $gCfg{maxtime};

    foreach($mintime, $maxtime) {
        $_ = POSIX::strftime(MINMAX_TIME_FMT, localtime($_));
    }

    return($actions, $discarded, $gCfg{commit}-1, $mintime, $maxtime);

}  #  End GetStats

###############################################################################
#  DoSsCmd
###############################################################################
sub DoSsCmd {
    my(@cmd) = @_;

    my $ok = &DoSysCmd(@cmd);

    $gSysOut =~ s/\x00//g; # remove null bytes
    $gSysOut =~ s/.\x08//g; # yes, I've seen VSS store backspaces in names!
    # allow all characters in the windows-1252 codepage: see http://de.wikipedia.org/wiki/Windows-1252
    $gSysOut =~ s/[\x00-\x09\x11\x12\x14-\x1F\x81\x8D\x8F\x90\x9D]/_/g; # just to be sure

}  #  End DoSsCmd

###############################################################################
#  DoSysCmd
###############################################################################
sub DoSysCmd {
    my(@args) = @_;
    my $allowfail = 1;

    unshift @args, $gCfg{ssphys};

    print join(" ", @args) .  "\n" if $gCfg{verbose};

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
    my($task, $leavestep) = @_;

    print "\nSETTING TASK $task\n" if $gCfg{verbose};

    my($sql, $sth);

    $sth = $gSth{'SYSTEMTASK'};

    if (!defined $sth) {
        $sql = <<"EOSQL";
UPDATE
    SystemInfo
SET
    task = ?
EOSQL

        $sth = $gSth{'SYSTEMTASK'} = $gCfg{dbh}->prepare($sql);
    }

    $sth->execute($task);

    $gCfg{task} = $task;

    &SetSystemStep(0) unless $leavestep;

}  #  End SetSystemTask

###############################################################################
#  SetSystemStep
###############################################################################
sub SetSystemStep {
    my($step) = @_;

    print "\nSETTING STEP $step\n" if $gCfg{verbose};

    my($sql, $sth);

    $sth = $gSth{'SYSTEMSTEP'};

    if (!defined $sth) {
        $sql = <<"EOSQL";
UPDATE
    SystemInfo
SET
    step = ?
EOSQL

        $sth = $gCfg{'SYSTEMSTEP'} = $gCfg{dbh}->prepare($sql);
    }

    $sth->execute($step);

    $gCfg{step} = $step;

}  #  End SetSystemStep

###############################################################################
#  ConnectDatabase
###############################################################################
sub ConnectDatabase {
    my $db = $gCfg{sqlitedb};

    if (-e $db && (!$gCfg{resume} ||
                   (defined($gCfg{task}) && $gCfg{task} eq TASK_INIT))) {

        unlink $db or &ThrowError("Could not delete existing database "
                                  .$gCfg{sqlitedb});
    }

    print "Connecting to database $db\n\n";

    $gCfg{dbh} = DBI->connect("dbi:SQLite:dbname=$db", '', '',
                              {RaiseError => 1, AutoCommit => 1})
        or die "Couldn't connect database $db: $DBI::errstr";

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
    if (defined($gCfg{task}) && $gCfg{task} eq TASK_INIT) {
        &InitSysTables;
    } else {
        &ReloadSysTables;
    }

    $gCfg{ssphys} = 'ssphys' if !defined($gCfg{ssphys});

}  #  End SetupGlobals

###############################################################################
#  InitSysTables
###############################################################################
sub InitSysTables {
    my($sql);

    $sql = <<"EOSQL";
CREATE TABLE
    Physical (
        physname    VARCHAR PRIMARY KEY,
        datapath    VARCHAR
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE TABLE
    NameLookup (
        offset      INTEGER,
        name        VARCHAR
    )
EOSQL

    $gCfg{dbh}->do($sql);

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

    $sql = <<"EOSQL";
CREATE TABLE
    PhysicalActionSchedule (
        schedule_id INTEGER PRIMARY KEY,
        action_id   INTEGER NOT NULL,
        $pa_sql
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE TABLE
    PhysicalActionChangeset (
        schedule_id INTEGER PRIMARY KEY,
        action_id   INTEGER NOT NULL,
        $pa_sql
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE TABLE
    PhysicalActionRetired (
        retired_id INTEGER PRIMARY KEY,
        commit_id INTEGER NOT NULL,
        changeset INTEGER NOT NULL,
        schedule_id INTEGER NOT NULL,
        action_id   INTEGER NOT NULL,
        $pa_sql
    )
EOSQL

    $gCfg{dbh}->do($sql);


    $sql = <<"EOSQL";
CREATE TABLE
    PhysicalActionDiscarded (
        discarded_id INTEGER PRIMARY KEY,
        commit_id INTEGER NOT NULL,
        changeset INTEGER NOT NULL,
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

    my @cfgitems = qw(task step ssphys tempdir starttime);

    my $fielddef = join(",\n        ",
                        map {sprintf('%-12.12s VARCHAR', $_)} @cfgitems);

    $sql = <<"EOSQL";
CREATE TABLE
    SystemInfo (
        $fielddef
    )
EOSQL

    $gCfg{dbh}->do($sql);

    my $fields = join(', ', @cfgitems);
    my $args = join(', ', map {"'" . $_  . "'"} @cfgitems);

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
    my($sql, $sth, $sthup, $row, $field, $val);

    $sql = "SELECT * FROM SystemInfo";

    $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute();

    $row = $sth->fetchrow_hashref();

FIELD:
    while (($field, $val) = each %$row) {
        if (defined($gCfg{$field})) { # allow user to override saved vals
            $sql = "UPDATE SystemInfo SET $field = ?";
            $sthup = $gCfg{dbh}->prepare($sql);
            $sthup->execute($gCfg{$field});
        } else {
            $gCfg{$field} = $val;
        }
    }

    $sth->finish();
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
    $gCfg{tempdir} = TEMPDIR if !defined($gCfg{tempdir});
    $gCfg{repo} = REPO if !defined($gCfg{repo});
    $gCfg{repo} = abs_path($gCfg{repo});
    $gCfg{vssdir} = abs_path($gCfg{vssdir});
    $gCfg{vssdatadir} = File::Spec->catdir($gCfg{vssdir}, 'data');
    $gCfg{revtimerange} = REVTIMERANGE unless defined($gCfg{revtimerange}) && $gCfg{revtimerange} > 0;

    if (! -d $gCfg{repo}) {
        die "repo directory '$gCfg{repo}' is not a directory";
    }

    # set up these items now
    $git_image{"@{[VSSDB_ROOT]}"} = $gCfg{repo};

    if (! -d $gCfg{vssdatadir}) {
        die "The VSS database '$gCfg{vssdir}' "
            . "does not appear to be a valid VSS database, as there's no 'data' directory.";
    }

    if (defined($gCfg{author_info}) && ! -r $gCfg{author_info}) {
        die "author_info file '$gCfg{author_info}' is not readable";
    } else {
        open my $info, $gCfg{author_info} or die "Could not open $gCfg{author_info}: $!";
        my $err = 0;

        while (<$info>) {
            my ($username, $author, $author_email) = split(/\t/);
            if (defined $username) {
                if (!defined $author) {
                    ++$err;
                    print "Undefined author for username `$username'\n";
                } elsif (defined $author && $author eq '') {
                    ++$err;
                    print "Empty author for username `$username'\n";
                }

                if (!defined $author_email) {
                    ++$err;
                    print "Undefined author email for username `$username'\n";
                } elsif (defined $author_email && $author_email eq '') {
                    ++$err;
                    print "Empty author email for username `$username'\n";
                }
            }

            $author_map->{$username} = { name => $author, email => $author_email };
        }
        close $info;

        die "author file '$gCfg{author_info}' had errors." if $err;
    }

    $gCfg{sqlitedb} = File::Spec->catfile($gCfg{tempdir}, 'vss_data.db');

    # XML output from ssphysout placed here.
    $gCfg{ssphysout} = File::Spec->catfile($gCfg{tempdir}, 'ssphysout');
    $gCfg{encoding} = ENCODING if !defined($gCfg{encoding});

    # All sorts of working data placed here
    mkdir $gCfg{tempdir} unless (-d $gCfg{tempdir});

    # Directories for holding VSS revisions
    $gCfg{vssdata} = File::Spec->catdir($gCfg{tempdir}, 'vssdata');

    # Directory for implementing file share/pin/branch.
    # All VSS_FILE entries, not just those shared/pinned will be linked here.
    $gCfg{links} = File::Spec->catdir($gCfg{tempdir}, 'links');

    $gCfg{resume} = 1 if defined $gCfg{task} && ($gCfg{task} ne TASK_INIT);

    if ($gCfg{resume} && !-e $gCfg{sqlitedb}) {
        warn "WARNING: --resume set but no database exists; "
            . "starting new conversion...";
        $gCfg{resume} = 0;
    }

    if ($gCfg{debug}) {
        $gCfg{verbose} = 1;
    }
    $gCfg{timing} = 0 unless defined $gCfg{timing};

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

    $gCfg{commit} = 1;
    $gCfg{changeset} = 1;

    ### Don't go past here if resuming a previous run ###
    if ($gCfg{resume}) {
        return 1;
    }

    rmtree($gCfg{vssdata}) if (-e $gCfg{vssdata});
    mkdir $gCfg{vssdata};
    rmtree($gCfg{links}) if (-e $gCfg{links});
    mkdir $gCfg{links};

    &WriteDestroyedPlaceholderFiles();

    $gCfg{ssphys} ||= 'ssphys';

    $gCfg{task} = TASK_INIT;
    $gCfg{step} = 0;
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

USAGE: perl vss2svn.pl --vssdir <dir> --author_info <file> [options]

REQUIRED PARAMETERS:
    --vssdir <dir>  : Directory where VSS database is located. This should be
                      the directory in which the "srcsafe.ini" file is located.
    --author_info <file>   : Tab separated file of <username> <author> <author_email>
                             where <username> is a VSS username

OPTIONAL PARAMETERS:
    --ssphys <path>   : Full path to ssphys.exe program; uses PATH otherwise
    --tempdir <dir>   : Temp directory to use during conversion;
                        default is '@{[TEMPDIR]}'
    --repo <directory> : specify the git repo to use;
                         default is '@{[REPO]}'.  It is assumed that it has been
                         initialized with 'git init' and contains appropriate
                         settings files (e.g, .gitignore, .gitattributes, etc.).
    --revtimerange <sec> : specify the maximum time difference (in seconds)
                           between two VSS actions that are treated as one git commit;
                           default is @{[REVTIMERANGE]} seconds (== 1hour).
                           Must be > 0.

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

    my ($changeset_count) = $gCfg{dbh}->selectrow_array('SELECT COUNT(*) FROM PhysicalActionChangeset');
    my $sth = $gCfg{dbh}->prepare('INSERT INTO PhysicalActionSchedule '
                                  . 'SELECT NULL AS schedule_id, * '
                                  . 'FROM PhysicalAction '
                                  . 'WHERE timestamp >= ? '
                                  . '  AND timestamp < ? '
                                  . '  AND action_id NOT IN '
                                  . '  (SELECT action_id FROM PhysicalActionSchedule '
                                  . '   UNION ALL SELECT action_id FROM PhysicalActionRetired '
                                  . '   UNION ALL SELECT action_id FROM PhysicalActionDiscarded) '
                                  . 'ORDER BY timestamp ASC, priority ASC, parentdata DESC');
    if (defined $changeset_count && $changeset_count > 0) {
        # We have unused data from the last scheduling pass, let's use it.
        $gCfg{dbh}->do('INSERT INTO PhysicalActionSchedule '
                       . 'SELECT * FROM PhysicalActionChangeset');
        $gCfg{dbh}->do('DELETE FROM PhysicalActionChangeset');

        # need to reset time, since there may be two commits in the same timestamp
        ($timestamp) = $gCfg{dbh}->selectrow_array('SELECT timestamp '
                                                   . 'FROM PhysicalActionSchedule '
                                                   . 'WHERE schedule_id = (SELECT MIN(schedule_id) FROM PhysicalActionSchedule)');
    }

    # This slides the window down.
    my $should_schedule = $sth->execute($timestamp, $timestamp+$gCfg{revtimerange});

    if (defined $should_schedule && $should_schedule > 0) {
        print "timestamp range: $timestamp - " . ($timestamp+$gCfg{revtimerange}) . "\n";
        &CheckAffinity();
        &ScheduleRevTime();
    }

    &GetOneChangeset($timestamp);
}

###############################################################################
#  ScheduleRevTime
###############################################################################
sub ScheduleRevTime {
    my($sth, $rows);
    state $index = 0;

    $sth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalActionSchedule ORDER BY schedule_id');

    my $startover_count = 0;
    # We may end up here a few times as we schedule
  STARTOVER:
    # deep clone these so we can simulate
    my $giti = dclone(\%git_image);

    # start scheduling
    $sth->execute();
    $rows = $sth->fetchall_arrayref( {} );

    # This seems to be a kind of insertion sort, give it a bound
    die "failed to schedule too many times" if $startover_count > ((scalar @$rows)*(scalar @$rows));

  ROW:
    foreach my $row (@$rows) {
        if ($index == 0
            && $row->{physname} eq VSSDB_ROOT
            && $row->{actiontype} eq ACTION_ADD
            && $row->{itemname} eq "") {
            # first time through, setting up the VSS root project
            # we don't need this one
            ++$index;
            $gCfg{dbh}->do("INSERT INTO PhysicalActionDiscarded "
                           . "SELECT NULL AS discarded_id, "
                           . "$gCfg{commit} AS commit_id, $gCfg{changeset} AS changeset, * "
                           . "FROM PhysicalActionSchedule WHERE schedule_id = $row->{schedule_id} "
                           . "ORDER BY schedule_id");
            $gCfg{dbh}->do("DELETE FROM PhysicalActionSchedule WHERE schedule_id = $row->{schedule_id}");
            next ROW;
        }

        my ($path, $parentpath);

        if (defined $row->{parentphys}) {
            my $rescheduled = 0;
            if (!defined $giti->{$row->{parentphys}}) {
                # we are out of schedule

#                    print "out of order: parentphys " . $row->{parentphys} . " physname: " . $row->{physname} . "\n";
#                    print "giti: " . Dumper($giti) . "\n";

                if ($row->{actiontype} eq ACTION_ADD || $row->{actiontype} eq ACTION_SHARE) {
                    # we are added out of schedule
                    my $tth;
                    my $ooo;

#                    $tth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalActionSchedule '
#                                               . 'WHERE timestamp = ? '
#                                               . 'ORDER BY schedule_id');
#                    $tth->execute($row->{timestamp});
#                    $ooo = $tth->fetchall_arrayref();
#                    print "slice entries before: " . Dumper($ooo) . "\n";

                    # grab all the out of order entries
                    $tth = $gCfg{dbh}->prepare('SELECT schedule_id, action_id FROM PhysicalActionSchedule '
                                               . 'WHERE parentphys = ? AND timestamp = ? '
                                               . 'ORDER BY schedule_id');
                    $tth->execute($row->{parentphys}, $row->{timestamp});
                    my $ooo_data = $tth->fetchall_arrayref({});

                    # throw the out of order ones into a new table
                    $tth = $gCfg{dbh}->prepare('CREATE TEMPORARY TABLE tmp AS '
                                               . ' SELECT * FROM PhysicalActionSchedule '
                                               . ' WHERE schedule_id IN '
                                               . ' (SELECT schedule_id FROM PhysicalActionSchedule '
                                               . '  WHERE parentphys = ? AND timestamp = ?)');
                    $tth->execute($row->{parentphys}, $row->{timestamp});

                    # clear out the out of order records
                    $gCfg{dbh}->do('DELETE FROM PhysicalActionSchedule '
                                   . 'WHERE schedule_id IN (SELECT schedule_id FROM tmp)');

                    # count in order entries
                    $tth = $gCfg{dbh}->prepare('SELECT MAX(schedule_id) FROM PhysicalActionSchedule '
                                               . 'WHERE timestamp = ? AND physname = ?');
                    $tth->execute($row->{timestamp}, $row->{parentphys});
                    my $max_sched = $tth->fetchall_arrayref()->[0][0];

                    if (!defined $max_sched) {
                        # The contents of tmp is duplicate from the child.
                        # We've already deleted the offending entry from PhysicalActionSchedule.
                        $tth = $gCfg{dbh}->prepare('SELECT schedule_id FROM PhysicalActionSchedule '
                                                   . 'WHERE timestamp = ? AND physname = ?');
                        $tth->execute($row->{timestamp}, $row->{physname});
                        $max_sched = $tth->fetchall_arrayref();
                        if (scalar @$max_sched == 1) {
                            $gCfg{dbh}->do("INSERT INTO PhysicalActionDiscarded "
                                           . "SELECT NULL AS discarded_id, "
                                           . "$gCfg{commit} AS commit_id, $gCfg{changeset} AS changeset, * "
                                           . "FROM tmp ORDER by schedule_id");
                            $gCfg{dbh}->do('DROP TABLE tmp');
                            ++$startover_count;
                            goto STARTOVER;
                        }
                        undef $max_sched;
                    }

#                    print "max sched: $max_sched\n";

                    $tth = $gCfg{dbh}->prepare('SELECT schedule_id, action_id FROM PhysicalActionSchedule '
                                               . 'WHERE timestamp = ? AND schedule_id > ? '
                                               . 'ORDER BY schedule_id');
                    $tth->execute($row->{timestamp}, $ooo_data->[0]{schedule_id});
                    $ooo = $tth->fetchall_arrayref({});

                    # renumber in order entries
                    my $idx = 0;
                    foreach my $o (@$ooo) {
                        $gCfg{dbh}->do('UPDATE PhysicalActionSchedule SET schedule_id='
                                       . ($ooo_data->[0]{schedule_id}+$idx)
                                       . ' WHERE schedule_id = ' . $o->{schedule_id}
                                       . ' AND action_id = ' . $o->{action_id});
                        ++$idx;
                    }


                    $tth = $gCfg{dbh}->prepare('SELECT * FROM tmp');
                    $tth->execute();
                    $ooo = $tth->fetchall_arrayref();

#                    print "out of order: " . Dumper($ooo) . "\n";

                    # renumber the out of order entries
                    $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
                    eval {
                        my $idx2 = 0;
                        foreach my $o (@$ooo_data) {
                            my $j = ($ooo_data->[0]{schedule_id}+$idx);
                            print "out of order: $j $o->{schedule_id}\n" if $gCfg{debug};
                            my $rv = $gCfg{dbh}->do("UPDATE tmp SET schedule_id=$j "
                                                    . "WHERE schedule_id = $o->{schedule_id} "
                                                    . "AND action_id = $o->{action_id}");
#                        print "rv: $rv\n";
                            ++$idx;
                            ++$idx2;
                        }
                    };
                    if ($@) {
                        warn "Transaction aborted because $@";
                        eval { $gCfg{dbh}->rollback };
                        die "Failed to reorder out of order items: timestamp: $row->{timestamp}";
                    } else {
                        $gCfg{dbh}->commit;
                    }

#                    $tth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalActionSchedule '
#                                                  . 'WHERE timestamp = ? '
#                                                  . 'ORDER BY schedule_id');
#                    $tth->execute($row->{timestamp});
#                    $ooo = $tth->fetchall_arrayref();
#                    print "in order renumbered: " . Dumper($ooo) . "\n";

#                    $tth = $gCfg{dbh}->prepare('SELECT * FROM tmp');
#                    $tth->execute();
#                    $ooo = $tth->fetchall_arrayref();
#                    print "out of order renumbered: " . Dumper($ooo) . "\n";

                    $gCfg{dbh}->do('INSERT INTO PhysicalActionSchedule SELECT * FROM tmp');
                    $gCfg{dbh}->do('DROP TABLE tmp');

#                    $tth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalActionSchedule '
#                                               . 'WHERE timestamp = ? '
#                                               . 'ORDER BY schedule_id');
#                    $tth->execute($row->{timestamp});
#                    $ooo = $tth->fetchall_arrayref();
#                    print "slice entries after: " . Dumper($ooo) . "\n";

                    $rescheduled = 1;
                }
                if ($rescheduled) {
#                    print "rescheduling " . $row->{actiontype} . " for " . $row->{parentphys} . "\n";
                    ++$startover_count;
                    goto STARTOVER;
                }
            }

            $parentpath = $giti->{$row->{parentphys}};
            $path = ($row->{itemtype} == VSS_PROJECT)
                ? File::Spec->catdir($parentpath, $row->{itemname})
                : File::Spec->catfile($parentpath, $row->{itemname});
        } else {
            # presumably this is a child entry
            # pick a path to update

            if (defined $row->{physname}
                && defined $giti->{$row->{physname}}) {
                $path = @{$giti->{$row->{physname}}}[0];
                $parentpath = dirname($path);
            }
        }

        &UpdateGitRepository($row, $parentpath, $path, $giti, 1, undef);
    }
    print "done scheduling -- " . (scalar @$rows) . " rows \n";
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
    my $ath = $gCfg{dbh}->prepare('SELECT DISTINCT timestamp '
                                  . 'FROM PhysicalActionSchedule '
                                  . 'ORDER BY timestamp');
    $ath->execute();
    my $timestamps = $ath->fetchall_arrayref();
    foreach my $t (@$timestamps) {
        my $timestamp = $t->[0];
        my $rowcount;

        ($rowcount) = $gCfg{dbh}->selectrow_array('SELECT COUNT(*) FROM PhysicalActionSchedule '
                                                  . ' WHERE timestamp = ? ORDER BY schedule_id',
                                                  undef,
                                                  $timestamp);
        if ($rowcount > 1) {
            $sth = $gCfg{dbh}->prepare('CREATE TEMPORARY TABLE tmp_affinity AS '
                                       . ' SELECT 0 AS affinity, * FROM PhysicalActionSchedule '
                                       . ' WHERE timestamp = ? ORDER BY schedule_id');
            $sth->execute($timestamp);

            # grab identifying data
            $sth = $gCfg{dbh}->prepare('SELECT schedule_id, action_id '
                                       . 'FROM tmp_affinity ORDER BY schedule_id');
            $sth->execute();
            my $ooo_data = $sth->fetchall_arrayref({});

            # In this scheme a negative value means pull up in the schedule,
            # 0 means no change, positive, move down the schedule.

            # check affinity with timestamp not equal to this one
            # of previously scheduled row
            $sth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalActionSchedule '
                                       . 'WHERE schedule_id = '
                                       . '   (SELECT MAX(schedule_id) '
                                       . '    FROM PhysicalActionSchedule '
                                       . '    WHERE timestamp = '
                                       . '          (SELECT MAX(timestamp) '
                                       . '           FROM PhysicalActionSchedule '
                                       . '           WHERE timestamp < ?)) LIMIT 1');
            $sth->execute($timestamp);
            my $lrow;
            while (defined($lrow = $sth->fetchrow_hashref())) {
                &UpdateRowAffinity($lrow,-1);
            }

            # check affinity with timestamp not equal to this one
            # of next row. This operation might not be a good idea --
            # these really aren't scheduled yet!
            $sth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalActionSchedule '
                                       . 'WHERE schedule_id = '
                                       . '   (SELECT MIN(schedule_id) '
                                       . '    FROM PhysicalActionSchedule '
                                       . '    WHERE timestamp = '
                                       . '          (SELECT MIN(timestamp) '
                                       . '           FROM PhysicalActionSchedule '
                                       . '           WHERE timestamp > ?)) LIMIT 1');
            $sth->execute($timestamp);
            while (defined($lrow = $sth->fetchrow_hashref())) {
                &UpdateRowAffinity($lrow,1);
            }

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

                $gCfg{dbh}->begin_work or die $gCfg{dbh}->errstr;
                eval {
                    my $i = 0;
                    foreach my $o (@oids) {
                        my $m = $ino_data->[$i];
                        if ($o != $m->{schedule_id}) {
                            $gCfg{dbh}->do("UPDATE tmp_affinity SET schedule_id = $o "
                                           . "WHERE schedule_id = $m->{schedule_id} "
                                           ."AND action_id = $m->{action_id}");
                        }
                        ++$i;
                    }
                };
                if ($@) {
                    warn "Transaction aborted because $@";
                    eval { $gCfg{dbh}->rollback };
                    die "Failed to update affinity at time $timestamp";
                } else {
                    $gCfg{dbh}->commit;
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
}

###############################################################################
#  UpdateRowAffinity
###############################################################################
sub UpdateRowAffinity {
    my ($lrow, $direction) = @_;

    my $rth = $gCfg{dbh}->prepare("UPDATE tmp_affinity SET affinity = affinity+$direction WHERE author = ?");
    $rth->execute($lrow->{author});

    if (defined $lrow->{comment}) {
        $rth = $gCfg{dbh}->prepare("UPDATE tmp_affinity SET affinity = affinity+$direction WHERE comment = ?");
        $rth->execute($lrow->{comment});
    } else {
        $gCfg{dbh}->do("UPDATE tmp_affinity SET affinity = affinity+$direction WHERE comment IS NULL");
    }

    if ($lrow->{actiontype} eq ACTION_LABEL) {
        $gCfg{dbh}->do("UPDATE tmp_affinity SET affinity = affinity+$direction WHERE actiontype = '@{[ACTION_LABEL]}'");

        if (defined $lrow->{label}) {
            $rth = $gCfg{dbh}->prepare("UPDATE tmp_affinity SET affinity = affinity+$direction "
                                       . "WHERE actiontype = '@{[ACTION_LABEL]}' AND label = ?");
            $rth->execute($lrow->{label});
        } else {
            $gCfg{dbh}->do("UPDATE tmp_affinity SET affinity = affinity+$direction "
                                . "WHERE actiontype = '@{[ACTION_LABEL]}' AND label IS NULL");
        }
    }
 }

###############################################################################
#  GetOneChangeset
###############################################################################
sub GetOneChangeset {
    my($timestamp) = @_;
    my $isth;
    my $dsth;
    my $dbgsql = 'SELECT COUNT(*) FROM PhysicalActionSchedule';
    my $dbgcnt;

    $isth = $gCfg{dbh}->prepare('INSERT INTO PhysicalActionChangeset '
                                . 'SELECT * FROM PhysicalActionSchedule WHERE schedule_id >= ?');

    $dsth = $gCfg{dbh}->prepare('DELETE FROM PhysicalActionSchedule WHERE schedule_id >= ?');

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
        ($dbgcnt) = $gCfg{dbh}->selectrow_array($dbgsql);
        print "scheduling timestamp $timestamp with $dbgcnt rows\n";
    }

    # Any leftovers are moved to PhysicalActionChangeset
    # for subsequent calls to SchedulePhysicalActions
    my $schedule_id;

    # dump all entries incuding and after the first mismatch of author
    # It's at least two changesets in this case.
    ($schedule_id) = $gCfg{dbh}->selectrow_array('SELECT schedule_id '
                                                 . 'FROM PhysicalActionSchedule '
                                                 . 'WHERE author NOT IN '
                                                 . '(SELECT author '
                                                 . ' FROM PhysicalActionSchedule '
                                                 . ' WHERE timestamp = ? ORDER BY schedule_id LIMIT 1) '
                                                 . 'ORDER BY schedule_id LIMIT 1',
                                                 undef,
                                                 $timestamp);
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }

    if ($gCfg{debug}) {
        ($dbgcnt) = $gCfg{dbh}->selectrow_array($dbgsql);
        my $msg = "scheduling author ";
        if ($schedule_id) {
            print "$msg $schedule_id rows: $dbgcnt\n";
        } else {
            print "$msg undef rows: $dbgcnt\n";
        }
    }

    # dump all entries incuding and after the first mismatch of comments
    # N.B. comments may be NULL
    # Again, it's at least two changesets in this case.
    # parentdata = 0 means that there could be comments there.
    ($schedule_id) = $gCfg{dbh}->selectrow_array('SELECT MIN(B.schedule_id) '
                                                 . 'FROM (SELECT comment FROM PhysicalActionSchedule '
                                                 . '      WHERE parentdata = 0 ORDER BY schedule_id LIMIT 1) AS A '
                                                 . 'CROSS JOIN (SELECT schedule_id, comment FROM PhysicalActionSchedule '
                                                 . '            WHERE parentdata = 0) AS B '
                                                 . 'WHERE (A.comment IS NULL AND B.comment IS NOT NULL '
                                                 . '       OR A.comment IS NOT NULL AND B.comment IS NULL '
                                                 . '       OR A.comment IS NOT NULL AND B.comment IS NOT NULL '
                                                 . '          AND A.comment != B.comment)');

    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }

    if ($gCfg{debug}) {
        ($dbgcnt) = $gCfg{dbh}->selectrow_array($dbgsql);
        my $msg = "scheduling comment ";
        if ($schedule_id) {
            print "$msg $schedule_id rows: $dbgcnt\n";
        } else {
            print "$msg undef rows: $dbgcnt\n";
        }
    }

    # Label filter part 1
    # When the first item on the schedule is (or is not) a LABEL, remove the first
    # non-LABEL (or LABEL) from the schedule and any subsequent entries

    ($schedule_id) = $gCfg{dbh}->selectrow_array("SELECT MIN(B.schedule_id) "
                                                 . "FROM (SELECT actiontype FROM PhysicalActionSchedule "
                                                 . "      WHERE parentdata = 0 ORDER BY schedule_id LIMIT 1) AS A "
                                                 . "CROSS JOIN (SELECT schedule_id, actiontype FROM PhysicalActionSchedule "
                                                 . "            WHERE parentdata = 0) AS B "
                                                 . "WHERE (A.actiontype = '@{[ACTION_LABEL]}' "
                                                 . "       AND B.actiontype != '@{[ACTION_LABEL]}') "
                                                 . "   OR (A.actiontype != '@{[ACTION_LABEL]}' "
                                                 . "       AND B.actiontype = '@{[ACTION_LABEL]}')");
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }

    if ($gCfg{debug}) {
        ($dbgcnt) = $gCfg{dbh}->selectrow_array($dbgsql);
        my $msg = "scheduling label pre ";
        if ($schedule_id) {
            print "$msg $schedule_id rows: $dbgcnt\n";
        } else {
            print "$msg undef rows: $dbgcnt\n";
        }
    }

    # dump all entries incuding and after the first mismatch of labels
    # N.B. labels may be NULL
    # Again, it's at least two labels. Even though there are no changes,
    # in a label how we are handling labels makes separating differing
    # labels into a changeset important.
    # parentdata = 0 means that there could be labels there.
    # This should be sufficient to isolate LABEL actions, since other
    # actions won't have label data.
    ($schedule_id) = $gCfg{dbh}->selectrow_array("SELECT MIN(B.schedule_id) "
                                                 . "FROM (SELECT actiontype, label FROM PhysicalActionSchedule "
                                                 . "      WHERE parentdata = 0 ORDER BY schedule_id LIMIT 1) AS A "
                                                 . "CROSS JOIN (SELECT schedule_id, actiontype, label FROM PhysicalActionSchedule "
                                                 . "            WHERE parentdata = 0) AS B "
                                                 . "WHERE A.actiontype = '@{[ACTION_LABEL]}' "
                                                 . "AND (A.label IS NULL AND B.label IS NOT NULL "
                                                 . "     OR A.label IS NOT NULL AND B.label IS NULL "
                                                 . "     OR A.label IS NOT NULL AND B.label IS NOT NULL AND A.label != B.label)");
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }

    if ($gCfg{debug}) {
        ($dbgcnt) = $gCfg{dbh}->selectrow_array($dbgsql);
        my $msg = "scheduling label ";
        if ($schedule_id) {
            print "$msg $schedule_id rows: $dbgcnt\n";
        } else {
            print "$msg undef rows: $dbgcnt\n";
        }
    }

    # * most directory actions
    # If the topmost scheduled action is one of the actions in the set
    # delete everything else from the schedule.  Otherwise if one is anywhere
    # else on the schedule, remove it and everything after it.
    ($schedule_id) = $gCfg{dbh}->selectrow_array("SELECT MIN(CASE schedule_id "
                                                 . "           WHEN (SELECT MIN(schedule_id) FROM PhysicalActionSchedule) "
                                                 . "           THEN schedule_id+1 "
                                                 . "           ELSE schedule_id "
                                                 . "           END) "
                                                 . "FROM PhysicalActionSchedule "
                                                 . "WHERE itemtype = @{[VSS_PROJECT]} AND actiontype IN "
                                                 . "('@{[ACTION_RESTOREDPROJECT]}', '@{[ACTION_RENAME]}', "
                                                 . "'@{[ACTION_DELETE]}', '@{[ACTION_DESTROY]}', '@{[ACTION_RECOVER]}', "
                                                 . "'@{[ACTION_RESTORE]}')");
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }

    if ($gCfg{debug}) {
        ($dbgcnt) = $gCfg{dbh}->selectrow_array($dbgsql);
        my $msg = "scheduling dir actions ";
        if ($schedule_id) {
            print "$msg $schedule_id rows: $dbgcnt\n";
        } else {
            print "$msg undef rows: $dbgcnt\n";
        }
    }

    # * same file touched more than once
    # SHARE and BRANCH are pretty benign, other actions potentially
    # change files.
    ($schedule_id) = $gCfg{dbh}->selectrow_array("SELECT MIN(A.schedule_id) "
                                                 . "FROM (SELECT schedule_id, actiontype, physname FROM PhysicalActionSchedule "
                                                 . "      WHERE parentdata = 1 ORDER BY schedule_id) AS A "
                                                 . "CROSS JOIN "
                                                 . "     (SELECT schedule_id, physname FROM PhysicalActionSchedule "
                                                 . "       WHERE parentdata = 1 ORDER BY schedule_id) AS B "
                                                 . "WHERE A.physname = B.physname AND A.schedule_id > B.schedule_id "
                                                 . "AND A.actiontype NOT IN ('@{[ACTION_SHARE]}', '@{[ACTION_BRANCH]}')");
    if ($schedule_id) {
        $isth->execute($schedule_id);
        $dsth->execute($schedule_id);
    }

    if ($gCfg{debug}) {
        ($dbgcnt) = $gCfg{dbh}->selectrow_array($dbgsql);
        my $msg = "scheduling same file touched ";
        if ($schedule_id) {
            print "$msg $schedule_id rows: $dbgcnt\n";
        } else {
            print "$msg undef rows: $dbgcnt\n";
        }
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

#    print "git_image: " . Dumper($git_image) . "\n";

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
    my($row, $parentpath, $path, $git_image, $simulated, $repo) = @_;

    my @delete_actions = (ACTION_DELETE, ACTION_DESTROY);
    my @restore_actions = (ACTION_RESTORE, ACTION_RESTOREDPROJECT);

    eval {
    for ($row->{itemtype}) {
        when (VSS_PROJECT) {
            for ($row->{actiontype}) {
                when (ACTION_ADD) {
                    if ($simulated) {
                        if (!defined $git_image->{$row->{physname}}) {
                            $git_image->{$row->{physname}} = $path;
                        }
                    } elsif (! -d $path) {
                        make_path($path);
                        if (!copy($gCfg{keepFile}, $path)) {
                            print "UpdateGitRepository: @{[ACTION_ADD]} @{[VSS_PROJECT]} copy $!\n";
                        } else {
                            $git_image->{$row->{physname}} = $path;
                            $repo->command('add', '--',  $path);
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
                    &DoMoveProject($repo, $path, $newpath, $git_image, $simulated, 1);
                }
                when (ACTION_MOVE_TO) {
                    # physname directory inode to move
                    # parentphys physname's parent directory
                    # info destination directory path
                    my $newpath = File::Spec->catdir($gCfg{repo}, $row->{info});

                    &DoMoveProject($repo, $path, $newpath, $git_image, $simulated, 1);
                }
                when (ACTION_MOVE_FROM) {
                    # physname moved directory inode
                    # parentphys destination's parent directory
                    # info source directory path
                    my $oldpath = File::Spec->catdir($gCfg{repo}, $row->{info});

                    &DoMoveProject($repo, $oldpath, $path, $git_image, $simulated, 0);
                }
                when (@delete_actions) {
                    if ($simulated) {
                        &RmProject($path, $git_image);
                    } elsif (-d $path) {
                        &RmProject($path, $git_image);
                        &GitRm($repo, $parentpath, $path, $row->{itemtype});
                    }
                }
                when (ACTION_RECOVER) {
                    &GitRecover($repo, $row, $path, $git_image, $simulated);
                }
                when (ACTION_LABEL) {
                    &GitLabel($row, $repo, $path, $simulated);
                }
            }
        }
        when (VSS_FILE) {
            for ($row->{actiontype}) {
                when (ACTION_ADD) {
                    # recorded in both the parent and child
                    if ($row->{parentdata}) {
                        if ($simulated) {
                            if (!defined $git_image->{$row->{physname}}) {
                                @{$git_image->{$row->{physname}}} = ("$path"); # may be on multiple paths
                            }
                        } elsif (! -f $path) {
                            # In the case of a destroyed file there's only the parent record
                            # we'll go ahead and add the file in case the child record is blown away
                            # by something.
                            my $link_file = File::Spec->catfile($gCfg{links}, $row->{physname});

                            if (! -f  $link_file) {
                                my ($action_id) = $gCfg{dbh}->selectrow_array("SELECT action_id "
                                                                              . "FROM PhysicalAction "
                                                                              . "WHERE physname = ? AND actiontype = '@{[ACTION_DESTROY]}' "
                                                                              . "LIMIT 1", # just in case
                                                                              undef, $row->{physname});
                                if (!copy((($action_id) ? $gCfg{destroyedFile} : $gCfg{indeterminateFile}),
                                          $link_file)) {  # touch the file
                                    print "UpdateGitRepository: @{[ACTION_ADD]} @{[VSS_FILE]} path `$link_file' copy $!\n";
                                }
                            }
                            link $link_file, $path;
                            $repo->command('add', '--',  $path);
                            &RemoveKeep($repo, $parentpath);
                            @{$git_image->{$row->{physname}}} = ("$path"); # may be on multiple paths
                        }
                    } elsif (defined $git_image->{$row->{physname}}
                             && ref($git_image->{$row->{physname}})) {
                        # we have child data here
                        my $link_file = File::Spec->catfile($gCfg{links}, $row->{physname});

                        $path = @{$git_image->{$row->{physname}}}[0];
                        my $exported = &ExportVssPhysFile($row->{physname}, $row->{version});

                        if (defined $exported) {
                            # copy the data to the link
                            if (!$simulated) {
                                if (!copy(File::Spec->catfile($exported,
                                                              $row->{physname} . '.' . $row->{version}),
                                          $link_file)) {
                                    print "UpdateGitRepository: @{[ACTION_ADD]} @{[VSS_FILE]} export path `$link_file' copy $!\n";
                                } else {
                                    $repo->command('add', '--',  $path);
                                    &RemoveKeep($repo, $parentpath);
                                }
                            }
                        }
                    } else {
                        # we have child data, but no parent data (yet)
                        # read it out for the link
                        # This step seems to happen chronologically first before
                        # writing the parent info, so they may be in different timestamps
                        my $link_file = File::Spec->catfile($gCfg{links}, $row->{physname});
                        my $exported = &ExportVssPhysFile($row->{physname}, $row->{version});

                        if (defined $exported) {
                            # copy the data to the link
                            if (!$simulated) {
                                if (!copy(File::Spec->catfile($exported,
                                                              $row->{physname} . '.' . $row->{version}),
                                          $link_file)) {
                                    print "UpdateGitRepository: @{[ACTION_ADD]} @{[VSS_FILE]} link path `$link_file' copy $!\n";
                                }
                            }
                        }

                    }
                }
                when (ACTION_RENAME) {
                    # these are only recorded in the parent
                    # Files may be renamed after DELETE(!) through a SHARE apparently
                    # so we need to check for their existence
                    my $newpath = File::Spec->catfile($parentpath, $row->{info});
                    $repo->command('mv',  $path,  $newpath) if !$simulated && -f $path;

                    # remove the old path, add the new path
                    @{$git_image->{$row->{physname}}} = grep {!/^\Q$path\E$/} @{$git_image->{$row->{physname}}};
                    push @{$git_image->{$row->{physname}}}, $newpath;
                }
                when (@delete_actions) {
                    # these are only recorded in the parent
                    my $path_re = qr/^\Q$path\E$/;

                    if ($simulated) {
                        @{$git_image->{$row->{physname}}} = grep {!/$path_re/} @{$git_image->{$row->{physname}}};
                        if (scalar @{$git_image->{$row->{physname}}} == 0) {
                            delete $git_image->{$row->{physname}};
                        }
                    } elsif (-f $path) {
                        @{$git_image->{$row->{physname}}} = grep {!/$path_re/} @{$git_image->{$row->{physname}}};

                        if (scalar @{$git_image->{$row->{physname}}} == 0) {
                            print "UpdateGitRepository delete @{[VSS_FILE]}: deleting git image $row->{physname}\n" if $gCfg{debug};
                            delete $git_image->{$row->{physname}};
                        }
                        &GitRm($repo, $parentpath, $path, $row->{itemtype});
                    }
                }
                when (ACTION_RECOVER) {
                    &GitRecover($repo, $row, $path, $git_image, $simulated);
                }
                when (@restore_actions) {
                    # XXX need example
                    # I don't think anything needs to be done here anyway
                    # but I could be mistaken.
                }
                when (ACTION_COMMIT) {
                    # only recorded in the child
                    my $exported = &ExportVssPhysFile($row->{physname}, $row->{version});

                    if (defined $exported) {
                        my $newver = File::Spec->catfile($exported, $row->{physname} . '.' . $row->{version});
                        my $link_file = File::Spec->catfile($gCfg{links}, $row->{physname});

                        if (!$simulated) {
                            if (!copy($newver, $link_file)) {
                                print "UpdateGitRepository: @{[ACTION_COMMIT]} @{[VSS_FILE]} path `$link_file' copy $!\n";
                            } else {
                                $repo->command('add', '--',  $path);
                            }
                        }
                    }
                }
                when (ACTION_SHARE) {
                    # only recorded in parent (but present in child XML)
                    my $oldpath = &SearchForPath($row->{physname}, $git_image);

                    if ($simulated) {
                        push @{$git_image->{$row->{physname}}}, $path;
                    } elsif (! -f $path) {
                        link $oldpath, $path;
                        push @{$git_image->{$row->{physname}}}, $path;
                        $repo->command('add', '--',  $path);
                        &RemoveKeep($repo, $parentpath);
                    }
                }
                when (ACTION_BRANCH) {
                    # branches recorded in parent and child
                    # no git action required
                    my $link_file = File::Spec->catfile($gCfg{links}, $row->{physname});

                    if ($row->{parentdata}) {
                        # set up bindings for the new branch
                        if ($simulated) {
                            @{$git_image->{$row->{physname}}} = ("$path");
                        } else {
                            if (!copy($path, $link_file)) { # should create new file
                                print "UpdateGitRepository: @{[ACTION_BRANCH]} @{[VSS_FILE]} path `$link_file' copy $!\n";
                            } else {
                                unlink $path; # decrement any link count
                                link $link_file, $path; # add $path as the new link
                                @{$git_image->{$row->{physname}}} = ("$path");
                            }
                            # shouldn't need to 'git add', it's a file with the same contents
                        }

                        # remove bindings for the old one
                        my $path_re = qr/^\Q$path\E$/;
                        @{$git_image->{$row->{info}}} = grep {!/$path_re/} @{$git_image->{$row->{info}}};
                        if (scalar @{$git_image->{$row->{info}}} == 0) {
                            print "UpdateGitRepository: @{[ACTION_BRANCH]} @{[VSS_FILE]}: deleting git image $row->{info}\n" if $gCfg{debug};
                            delete $git_image->{$row->{info}};
                        }
                    } elsif (! -f $link_file) {
                        # for some reason, the parent info is missing
                        # no parent info to link, just copy the link file
                        my $link_info = File::Spec->catfile($gCfg{links}, $row->{info});
                        if (!$simulated) {
                            if (!copy($link_info, $link_file)) { # should create new file
                                print "UpdateGitRepository: @{[ACTION_BRANCH]} @{[VSS_FILE]} path `$link_file' copy $!\n";
                            }
                        }
                    }
                }
                when (ACTION_PIN) {
                    my $link_file = File::Spec->catfile($gCfg{links}, $row->{physname});

                    if (defined $row->{info}) {
                        # this is an unpin
                    } else {
                        # this is a pin
                        # There's not a really good way to do this, since
                        # git doesn't suport this, nor do most Linux filesystems.
                        # Find the old version and copy it over...
                        my $exported = &ExportVssPhysFile($row->{physname}, $row->{version});
                        my $pinfile = $row->{physname} . '.' . $row->{version};
                        $link_file .= $row->{version};
                        if (defined $exported && !$simulated && ! -f $link_file) {
                            if (!copy(File::Spec->catfile($exported, $pinfile), $link_file)) {
                                print "UpdateGitRepository: @{[ACTION_PIN]} @{[VSS_FILE]} path `$link_file' copy $!\n";
                            }
                        }
                    }

                    if (!$simulated) {
                        unlink $path if -f $path; # get rid of pinned/unpinned file
                        link $link_file, $path;
                        $repo->command('add', '--',  $path);
                    }
                }
                when (ACTION_LABEL) {
                    &GitLabel($row, $repo, $path, $simulated);
                }
            }
        }
    }
    };

    if ($@) {
        print "An error ($@) occurred\n";
        print "git_image: " . Dumper(\%git_image) . "\n";
        print "row: " . Dumper($row) . "\n";
        exit(1);
    }

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

    if (!defined $dlabel || $dlabel eq '') {
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

    &git_setenv($username, $timestamp);
    $repo->command('commit', '-a', '--allow-empty-message', '--no-edit', '-m',  $comment);

    my $branch = $repo->command_oneline('symbolic-ref', '-q', '--short', 'HEAD');

    if ($branch !~ $master_re) {
        # back to master
        $repo->command('checkout', '-q', 'master');
    }
}

# setup the environment for GitCommit
sub git_setenv {
    my($username, $timestamp) = @_;
    my $map = $author_map->{$username};

    $ENV{'GIT_AUTHOR_NAME'} = $map->{name};
    $ENV{'GIT_AUTHOR_EMAIL'} = $map->{email};
    $ENV{'GIT_AUTHOR_DATE'} = POSIX::strftime(ISO8601_FMT, localtime($timestamp));
}

# create or checkout a branch for a label and add files to it from master
sub GitLabel {
    my($row, $repo, $path, $simulated) = @_;

    if (!$simulated) {
        my $branch = $repo->command_oneline('symbolic-ref', '-q', '--short', 'HEAD');
        my $tagname = get_valid_ref_name($row->{label}, $row->{timestamp});

        # "git checkout master" is hampered by absolute paths in this case
        # so we just strip off the repo dir
        my @tagnamedir = File::Spec->splitdir($path);
        my @repodir = File::Spec->splitdir($gCfg{repo});

        @tagnamedir = @tagnamedir[($#repodir+1)..$#tagnamedir];
        my $tmppath;
        if ($row->{itemtype} == VSS_FILE) {
            $tmppath = File::Spec->catfile(@tagnamedir);
        } else {
            $tmppath = File::Spec->catdir(@tagnamedir);
        }

        if (!defined $row->{label} || !defined $label_map->{$row->{label}}) {
            # create a new branch for this label
            # undef labels are not recorded in label map
            $repo->command('checkout', '-q', '--orphan',  $tagname);
            $repo->command('config', "branch." . $tagname . ".description",  $row->{comment}); # give it a description
            $repo->command('reset', '--hard'); # unmark all the "new" files from the commit.
            if (defined $row->{label} && $row->{label} ne '') {
                $label_map->{$row->{label}} = $tagname;
                print "Label `" . $row->{label} . "' is branch `$tagname'.\n";
            } else {
                print "undef label is branch `$tagname' at timestamp $row->{timestamp}.\n";
            }
        } elsif ($branch =~ $master_re) {
            $repo->command('checkout', '-q', $tagname);
        }
        $repo->command('checkout', '-q', 'master', '--',  $tmppath);
    }
}

# handle different kinds of moves
sub DoMoveProject {
    my($repo, $path, $newpath, $git_image, $simulated, $newtest) = @_;

    if ($simulated) {
        &MoveProject($path, $newpath, $git_image);
    } elsif ($newtest ? (! -d $newpath) : (-d $path)) {
        $repo->command('mv',  $path,  $newpath);
        # N.B. inode should _not_ have changed during move
        &MoveProject($path, $newpath, $git_image);
    }
}

# remove the directory keep file if there is one
sub RemoveKeep {
    my($repo, $parentpath) = @_;

    my $keep = File::Spec->catfile($parentpath, KEEP_FILE);

    $repo->command('rm', '-f', '-q', '--',  $keep) if -f $keep;
}

# handle the recover
sub GitRecover {
    my($repo, $row, $path, $git_image, $simulated) = @_;

    my ($action_id) = $gCfg{dbh}->selectrow_array("SELECT action_id "
                                                  . "FROM PhysicalAction "
                                                  . "WHERE physname = ? AND actiontype = '@{[ACTION_DESTROY]}' "
                                                  . "LIMIT 1", # just in case
                                                  undef, $row->{physname});
    if ($simulated) {
        for ($row->{itemtype}) {
            when (VSS_PROJECT) {
                if (!$action_id) {
                    $git_image->{$row->{physname}} = $path;
                }
            }
            when (VSS_FILE) {
                @{$git_image->{$row->{physname}}} = ("$path");
            }
        }
    } elsif (! -e $path) {
        for ($row->{itemtype}) {
            when (VSS_PROJECT) {
                # easier to recover from git
                if (!$action_id) {
                    my $rev = $repo->command_oneline('rev-list', '-n', '1', 'HEAD', '--',  $path);
                    $repo->command('checkout', '-q', "$rev^", '--',  $path);
                    $git_image->{$row->{physname}} = $path;
                } else {
                    # XXX don't know what to do here
                    # probably should do nothing anyway
                }
            }
            when (VSS_FILE) {
                my $link_file = File::Spec->catfile($gCfg{links}, $row->{physname});
                if (!$action_id) {
                    # These will exist in git history, bring them back.
                    # Must do it this way for RENAMEing SHAREd files after DELETE
                    link $link_file, $path;
                } else {
                    if (-f $link_file) {
                        # we have a backup from history (we were BRANCHed)
                        link $link_file, $path; # add $path as the new link
                    } else {
                        # no history backup, fake it
                        if (!copy($gCfg{destroyedFile}, $link_file)) {  # touch the file
                            print "UpdateGitRepository: @{[ACTION_ADD]} @{[VSS_FILE]} path `$link_file' copy $!\n";
                        } else {
                            link $link_file, $path;
                        }
                    }
                }
                $repo->command('add', '--',  $path);
                &RemoveKeep($repo, dirname($path));
                @{$git_image->{$row->{physname}}} = ("$path");
            }
        }
    }
}

sub GitRm {
    my($repo, $parentpath, $path, $itemtype) = @_;

    # add back the keep file before 'git rm', so we don't have to reset
    # inode bookkeeping
    my $keepfile = File::Spec->catfile($parentpath, KEEP_FILE);
    if (!copy($gCfg{keepFile}, $keepfile)) {
        print "GitRm: path `$keepfile' copy $!\n";
    }

    $repo->command('rm', ($itemtype == VSS_PROJECT ? '-rf' : '-f'), '-q', '--',  $path);

    # count the files in parentpath to see if the keep file should be added
    opendir(my $DIR, $parentpath);
    my $parentpath_dir_files = () = readdir $DIR;
    closedir $DIR;

    if ($parentpath_dir_files == 3) {
        $repo->command('add', '--',  $keepfile);
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
