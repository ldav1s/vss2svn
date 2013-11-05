#!/usr/bin/perl

use warnings;
use strict;

use v5.10.1;

use feature "switch";
use feature "state";

use Cwd 'abs_path';
use Getopt::Long;
use DBI;
use DBD::SQLite2;
use XML::Simple;
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
use Vss2Svn::ActionHandler;
use Vss2Svn::DataCache;
use Vss2Svn::SvnRevHandler;
use Vss2Svn::GitRepo;
use POSIX;
use Git;
use Data::Dumper;

require Encode;

use constant {
    TASK_INIT => 'INIT',
    TASK_LOADVSSNAMES => 'LOADVSSNAMES',
    TASK_FINDDBFILES => 'FINDDBFILES',
    TASK_GETPHYSHIST => 'GETPHYSHIST',
    TASK_MERGEPARENTDATA => 'MERGEPARENTDATA',
    TASK_MERGEMOVEDATA => 'MERGEMOVEDATA',
    TASK_REMOVETMPCHECKIN => 'REMOVETMPCHECKIN',
    TASK_MERGEUNPINPIN => 'MERGEUNPINPIN',
    TASK_BUILDCOMMENTS => 'BUILDCOMMENTS',
    TASK_BUILDACTIONHIST => 'BUILDACTIONHIST',
    TASK_GITREAD => 'GITREAD',
    TASK_IMPORTGIT => 'IMPORTGIT',
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

our(%gCfg, %gSth, %gErr, $gSysOut, %gNameLookup);

our $VERSION = '0.11.0-nightly.$LastChangedRevision$';
$VERSION =~ s/\$.*?(\d+).*\$/$1/; # get only the number out of the svn revision

# The git image is the physical layout of files in the git repo
# that get built up as we step through history.
# The git_image hash maps from VSS physname to inode (e.g. 'MBAAAAAA' => 1234).
my %git_image = ();

# The image_name hash maps inodes to filesystem paths.
# Projects (VSS directories) only have one parent. VSS files
# may have multiple parents through SHARE actions which are simulated
# in git (on Linux) by hard links.  git does not track that, but tracks
# file contents instead.
my %image_name = ();

my $label_map = ();
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
     # Initialize the git repo and a few in memory structures
     {
         task => TASK_GITREAD,
         handler => \&GitReadImage,
     },

#     # Merge data from parent records into child records where possible
#     {
#         task => TASK_MERGEPARENTDATA,
#         handler => \&MergeParentData,
#     },
#
#     # Merge data from move actions
#     {
#         task => TASK_MERGEMOVEDATA,
#         handler => \&MergeMoveData,
#     },
#     # Remove unnecessary Unpin/pin activities
#     {
#         task => TASK_MERGEUNPINPIN,
#         handler => \&MergeUnpinPinData,
#     },
#     # Rebuild possible missing comments
#     {
#         task => TASK_BUILDCOMMENTS,
#         handler => \&BuildComments,
#     },
#     # Take the history of physical actions and convert them to VSS
#     # file actions
#     {
#         task => TASK_BUILDACTIONHIST,
#         handler => \&BuildVssActionHistory,
#     },
#     # import to repository
#     {
#         task => TASK_IMPORTGIT,
#         handler => \&ImportToGit,
#     },
     # done state
     {
         task    => TASK_DONE,
         handler => sub { 1; },
     }
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
            . POSIX::strftime(Vss2Svn::GitRepo::ISO8601_FMT . "\n", localtime) . "\n";
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

    my $xs = XML::Simple->new(KeyAttr => [],
                              ForceArray => [qw(NameCacheEntry Entry)],);

    my $xml = $xs->XMLin($gSysOut);

    my $namesref = $xml->{NameCacheEntry} || return 1;

    my($entry, $count, $offset, $name);

    my $cache = Vss2Svn::DataCache->new('NameLookup')
        || &ThrowError("Could not create cache 'NameLookup'");

ENTRY:
    foreach $entry (@$namesref) {
        $count = $entry->{NrOfEntries};
        $offset = $entry->{offset};

        # The cache can contain 4 different entries:
        #   id=1: abbreviated DOS 8.3 name for file items
        #   id=2: full name for file items
        #   id=3: abbreviated 27.3 name for file items
        #   id=10: full name for project items
        # Both ids 1 and 3 are not of any interest for us, since they only
        # provide abbreviated names for different szenarios. We are only
        # interested if we have id=2 for file items, or id=10 for project
        # items.
        foreach $name (@{$entry->{Entry}}) {
            if ($name->{id} == 10 || $name->{id} == 2) {
                $cache->add($offset, $name->{content});
            }
        }
    }

    $cache->commit();
}  #  End LoadVssNames

###############################################################################
#  FindPhysDbFiles
###############################################################################
sub FindPhysDbFiles {

    my $cache = Vss2Svn::DataCache->new('Physical')
        || &ThrowError("Could not create cache 'Physical'");
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
                $cache->add(uc($_), $File::Find::name);
                ++$vssdb_cnt;
            },
         }, @dirs);

    print "Found $vssdb_cnt VSS database files at '$gCfg{vssdatadir}'\n" if $gCfg{verbose};

    $cache->commit();

}  #  End FindPhysDbFiles

###############################################################################
#  GetPhysVssHistory
###############################################################################
sub GetPhysVssHistory {
    my($sql, $sth, $row, $physname, $datapath);

    &LoadNameLookup;
    my $cache = Vss2Svn::DataCache->new('PhysicalAction', 1)
        || &ThrowError("Could not create cache 'PhysicalAction'");

    $sql = "SELECT * FROM Physical";
    $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute();

    my $xs = XML::Simple->new(ForceArray => [qw(Version)]);

    while (defined($row = $sth->fetchrow_hashref() )) {
        $physname = $row->{physname};
        $datapath = $row->{datapath};

        &GetVssPhysInfo($cache, $datapath, $physname, $xs);
    }

    $cache->commit();

}  #  End GetPhysVssHistory

###############################################################################
#  GetVssPhysInfo
###############################################################################
sub GetVssPhysInfo {
    my($cache, $datapath, $physname, $xs) = @_;

    print "datapath: \"$datapath\"\n" if $gCfg{debug};
    my @cmd = ('info', "-e$gCfg{encoding}", "$datapath");
    &DoSsCmd(@cmd);

    my $xml = $xs->XMLin($gSysOut);
    my $parentphys;

    my $iteminfo = $xml->{ItemInfo};

    if (!defined($iteminfo) || !defined($iteminfo->{Type}) ||
        ref($iteminfo->{Type})) {

        &ThrowWarning("Can't handle file '$physname'; not a project or file\n");
        return;
    }

    for ($iteminfo->{Type}) {
        when (VSS_PROJECT) {
            $parentphys = (uc($physname) eq Vss2Svn::ActionHandler::VSSDB_ROOT)?
                '' : &GetProjectParent($xml);
        }
        when (VSS_FILE) { $parentphys = undef; }
        default {
            &ThrowWarning("Can't handle file '$physname'; not a project or file\n");
            return;
        }
    }

    &GetVssItemVersions($cache, $physname, $parentphys, $xml);

}  #  End GetVssPhysInfo

###############################################################################
#  GetProjectParent
###############################################################################
sub GetProjectParent {
    my($xml) = @_;

    no warnings 'uninitialized';
    return $xml->{ItemInfo}->{ParentPhys} || undef;

}  #  End GetProjectParent

###############################################################################
#  GetVssItemVersions
###############################################################################
sub GetVssItemVersions {
    my($cache, $physname, $parentphys, $xml) = @_;

    return 0 unless defined $xml->{Version};

    my($parentdata, $version, $vernum, $action, $name, $actionid, $actiontype,
       $tphysname, $itemname, $itemtype, $parent, $user, $timestamp, $comment,
       $is_binary, $info, $priority, $sortkey, $label, $cachename);

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

VERSION:
    foreach $version (@{ $xml->{Version} }) {
        $action = $version->{Action};
        $name = $action->{SSName};
        $tphysname = $action->{Physical} || $physname;
        $user = $version->{UserName};

        $itemname = &GetItemName($name);

        $actionid = $action->{ActionId};
        $info = $gActionType{$actionid};

        if (!$info) {
            &ThrowWarning ("'$physname': Unknown action '$actionid'\n");
            next VERSION;
        }

        # check the linear order of timestamps. It could be done better, for
        # example checking the next version and calculate the middle time stamp
        # but regardless of what we do here, the result is erroneous, since it
        # will mess up the labeling.
        $timestamp = $version->{Date};
        if ($timestamp < $last_timestamp) {
            $timestamp = $last_timestamp + 1;
            &ThrowWarning ("'$physname': wrong timestamp at version "
                           . "'$version->{VersionNumber}'; setting timestamp to "
                           . "'$timestamp'");
        }
        $last_timestamp = $timestamp;

        $itemtype = $info->{type};
        $actiontype = $info->{action};

        if ($actiontype eq 'IGNORE') {
            next VERSION;
        }

        $comment = undef;
        $is_binary = 0;
        $info = undef;
        $parentdata = 0;
        $priority = 5;
        $label = undef;

        if ($version->{Comment} && !ref($version->{Comment})) {
            $comment = $version->{Comment} || undef;
        }

        # In case of Label the itemtype is the type of the item currently
        # under investigation
        if ($actiontype eq ACTION_LABEL) {
            my $iteminfo = $xml->{ItemInfo};
            $itemtype = $iteminfo->{Type};
        }

        # we can have label actions and labels attached to versions
        if (defined $action->{Label} && !ref($action->{Label})) {
            $label = $action->{Label};

            # append the label comment to a possible version comment
            if ($action->{LabelComment} && !ref($action->{LabelComment})) {
                if (defined $comment) {
                    print "Merging LabelComment and Comment for "
                        . "'$tphysname;$version->{VersionNumber}'\n"; # if $gCfg{verbose};
                    $comment .= "\n";
                }

                $comment .= $action->{LabelComment} || undef;
            }
        }

        if (defined($comment)) {
            $comment =~ s/(?:\r\n|\r(?!\n))/\n/g;
            $comment =~ s/^\s+//s;
            $comment =~ s/\s+$//s;
        }

        if ($itemtype == VSS_PROJECT && uc($physname) eq Vss2Svn::ActionHandler::VSSDB_ROOT
            && ref($tphysname)) {

            $tphysname = $physname;
            $itemname = '';
        } elsif ($physname ne $tphysname) {
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

        if ($itemtype == VSS_FILE && defined($xml->{ItemInfo})
            && defined($xml->{ItemInfo}->{Binary})) {
            $is_binary = $xml->{ItemInfo}->{Binary};
        }

        for ($actiontype) {
            when (ACTION_RENAME) {
                # if a rename, we store the new name in the action's 'info' field
                $info = &GetItemName($action->{NewSSName});
            }
            when (ACTION_BRANCH) {
                $info = $action->{Parent};
            }
            when (ACTION_MOVE_TO) {
                $info = $action->{DestPath};
                $info =~ s/^..(.*)$/$1/;
            }
            when (ACTION_MOVE_FROM) {
                $info = $action->{SrcPath};
                $info =~ s/^..(.*)$/$1/;
            }
        }


        $vernum = $version->{VersionNumber};

        # since there is no corresponding client action for PIN, we need to
        # enter the concrete version number here manually
        # In a share action the pinnedToVersion attribute can also be set
        $vernum = $action->{PinnedToVersion} if (defined $action->{PinnedToVersion});

        # for unpin actions also remeber the unpinned version
        $info = $action->{UnpinnedFromVersion} if (defined $action->{UnpinnedFromVersion});

        for ($actiontype) {
            when (ACTION_ADD) { $priority -= 4; }
            when (ACTION_SHARE) { $priority -= 3; }
            when (ACTION_PIN) { $priority -= 3; }
            when (ACTION_BRANCH) { $priority -= 2; }
        }

        # store the reversed physname as a sortkey; a bit wasteful but makes
        # debugging easier for the time being...
        $sortkey = reverse($tphysname);

        $cache->add($tphysname, $vernum, $parentphys, $actiontype, $itemname,
                    $itemtype, $timestamp, $user, $is_binary, $info, $priority,
                    $sortkey, $parentdata, $label, $comment);

        # Handle version labels as a secondary action for the same version
        # version labels and label action use the same location to store the
        # label. Therefore it is not possible to assign a version label to
        # version where the actiontype was LABEL. But ssphys will report the
        # same label twice. Therefore filter the Labeling versions here.
        if (defined $version->{Label} && !ref($version->{Label})
            && $actiontype ne ACTION_LABEL) {
            my ($labelComment);

            if ($version->{LabelComment} && !ref($version->{LabelComment})) {
                $labelComment = $version->{LabelComment};
            }
            else {
                $labelComment = "assigned label '$version->{Label}' to version $vernum of physical file '$tphysname'";
            }
            $cache->add($tphysname, $vernum, $parentphys, ACTION_LABEL, $itemname,
                        $itemtype, $timestamp, $user, $is_binary, $info, 5,
                        $sortkey, $parentdata, $version->{Label}, $labelComment);
        }
    }

}  #  End GetVssItemVersions

###############################################################################
#  GetItemName
###############################################################################
sub GetItemName {
    my($nameelem) = @_;

    my $itemname = $nameelem->{content};

    if (defined($nameelem->{offset})) {
        # see if we have a better name in the cache
        my $cachename = $gNameLookup{ $nameelem->{offset} };

        if (defined($cachename)) {
            print "Changing name of '$itemname' to '$cachename' from "
                  . "name cache\n" if $gCfg{debug};
            $itemname = $cachename;
        }
    }

    return $itemname;

}  #  End GetItemName

###############################################################################
#  LoadNameLookup
###############################################################################
sub LoadNameLookup {
    my($sth, $row);

    $sth = $gCfg{dbh}->prepare('SELECT offset, name FROM NameLookup');
    $sth->execute();

    while(defined($row = $sth->fetchrow_hashref() )) {
        $gNameLookup{ $row->{offset} } = Encode::decode_utf8( $row->{name} );
    }
}  #  End LoadNameLookup

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

            if ($dump_cnt % 100 == 0) {
                print "git_image: " . Dumper(\%git_image) . "\n";
                print "image_name: " . Dumper(\%image_name) . "\n";
                if ($dump_cnt == 100) {
                    exit(0);
                }
            }
            ++$dump_cnt;

            if (defined $row->{parentphys}) {
                print "parentphys: " . $row->{parentphys} .
                    " physname: " . $row->{physname} .
                    " timestamp: " .  $row->{timestamp} . "\n";
                $parentpath = $image_name{$git_image{$row->{parentphys}}};
                $path = ($row->{itemtype} == VSS_PROJECT)
                    ? File::Spec->catdir($parentpath, $row->{itemname})
                    : File::Spec->catfile($parentpath, $row->{itemname});
            } else {
                # presumably this is a child entry
                # pick a path to update
                if (defined $row->{physname}
                    && defined $git_image{$row->{physname}}
                    && defined $image_name{$git_image{$row->{physname}}}) {
                    $path = @{$image_name{$git_image{$row->{physname}}}}[0];
                    $parentpath = dirname($path);
                }
            }

            my $sim = 0; # not simulating here
            &UpdateGitRepository($row, $parentpath, $path, \%git_image, \%image_name, \$sim, $repo);
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
    foreach my $key (keys %image_name) {
        my $ary = $image_name{$key};
        my $base = shift @$ary;
        $base =~ s/^\Q$gCfg{repo}\E.//;

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


}

###############################################################################
#  MergeParentData
###############################################################################
sub MergeParentData {
    # VSS has a funny way of not placing enough information to rebuild history
    # in one data file; for example, renames are stored in the parent project
    # rather than in that item's data file. Also, it's sometimes impossible to
    # tell from a child record which was eventually shared to multiple folders,
    # which folder it was originally created in.

    # So, at this stage we look for any parent records which described child
    # actions, then update those records with data from the child objects. We
    # then delete the separate child objects to avoid duplication.

    &StopConversion;


    my($sth, $rows, $row);
    $sth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalAction '
                               . 'WHERE parentdata > 0');
    $sth->execute();

    # need to pull in all recs at once, since we'll be updating/deleting data
    $rows = $sth->fetchall_arrayref( {} );

    my($childrecs, $child, $id, $depth);
    my @delchild = ();

    foreach $row (@$rows) {
        $childrecs = &GetChildRecs($row);

        if (scalar @$childrecs > 1) {
            &ThrowWarning("Multiple child recs for parent rec "
                          . "'$row->{action_id}'");
        }

        $depth = &GetPathDepth($row);

        foreach $child (@$childrecs) {
            &UpdateParentRec($row, $child);
            push(@delchild, $child->{action_id});
        }
    }

    if (scalar @delchild > 0) {
        # just numbers here, no need to quote
        my $in_clause = join q{,}, @delchild;
        $gCfg{dbh}->do("DELETE FROM PhysicalAction WHERE action_id IN ($in_clause)");
    }

    1;

}  #  End MergeParentData

###############################################################################
#  GetPathDepth
###############################################################################
sub GetPathDepth {
    my($row) = @_;

    # If we've already worked out the depth of this row, return it immediately
    if ($row->{parentdata} > 1) {
        return $row->{parentdata};
    }

    my($maxParentDepth, $depth, $parents, $parent);

    # Get the row(s) corresponding to the parent(s) of this row, and work out
    # the maximum depth

    my $sql = <<"EOSQL";
SELECT
    *
FROM
    PhysicalAction
WHERE
    parentdata > 0
    AND physname = ?
    AND actiontype = ?
    AND timestamp <= ?
EOSQL

    my $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute( @{ $row }{qw(parentphys actiontype timestamp)} );

    $parents =  $sth->fetchall_arrayref( {} );
    $maxParentDepth = 0;
    foreach $parent (@$parents) {
        $depth = &GetPathDepth($parent);
        $maxParentDepth = ($depth > $maxParentDepth) ? $depth : $maxParentDepth;
    }

    # Depth of this path becomes one more than the maximum parent depth
    $depth = $maxParentDepth + 1;

    # Update the row for this record
    &UpdateDepth($row, $depth);

    return $depth;
}  #  End GetPathDepth

###############################################################################
#  UpdateDepth
###############################################################################
sub UpdateDepth {
    my($row, $depth) = @_;

    my $sql = <<"EOSQL";
UPDATE
    PhysicalAction
SET
    parentdata = ?
WHERE
    action_id = ?
EOSQL

    my $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute( $depth, $row->{action_id} );

}  #  End UpdateDepth

###############################################################################
#  GetChildRecs
###############################################################################
sub GetChildRecs {
    my($parentrec, $parentdata) = @_;

    # Here we need to find any child rows which give us additional info on the
    # parent rows. There's no definitive way to find matching rows, but joining
    # on physname, actiontype, timestamp, and author gets us close. The problem
    # is that the "two" actions may not have happened in the exact same second,
    # so we need to also look for any that are some time apart and hope
    # we don't get the wrong row.

    $parentdata = 0 unless defined $parentdata;
    $parentdata = 1 if $parentdata != 0;

    my $sql = <<"EOSQL";
SELECT
    *
FROM
    PhysicalAction
WHERE
    MIN(parentdata, 1) = ?
    AND physname = ?
    AND actiontype = ?
    AND author = ?
ORDER BY
    ABS(? - timestamp)
EOSQL

    my $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute( $parentdata, @{ $parentrec }{qw(physname actiontype author timestamp)} );

    return $sth->fetchall_arrayref( {} );
}  #  End GetChildRecs

###############################################################################
#  UpdateParentRec
###############################################################################
sub UpdateParentRec {
    my($row, $child) = @_;

    # The child record has the "correct" version number (relative to the child
    # and not the parent), as well as the comment info and whether the file is
    # binary

    my $comment;

    {
        no warnings 'uninitialized';
        $comment = "$row->{comment}\n$child->{comment}";
        $comment =~ s/^\n+//;
        $comment =~ s/\n+$//;
    }

    my $sql = <<"EOSQL";
UPDATE
    PhysicalAction
SET
    version = ?,
    is_binary = ?,
    comment = ?
WHERE
    action_id = ?
EOSQL

    my $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute( $child->{version}, $child->{is_binary}, $comment,
                  $row->{action_id} );

}  #  End UpdateParentRec

###############################################################################
#  MergeMoveData
###############################################################################
sub MergeMoveData {
    # Similar to the MergeParentData, the MergeMove Data combines two the src
    # and target move actions into one move action. Since both items are parents
    # the MergeParentData function can not deal with this specific problem

    my($sth, $rows, $row);

    $sth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalAction '
                               . "WHERE actiontype = '" . ACTION_MOVE_FROM . "'");
    $sth->execute();

    # need to pull in all recs at once, since we'll be updating/deleting data
    $rows = $sth->fetchall_arrayref( {} );

    my($childrecs, $child, $id);

    foreach $row (@$rows) {
        $row->{actiontype} = ACTION_MOVE_TO;
        $childrecs = &GetChildRecs($row, 1);

        my $source = undef;
        my $target = $row->{parentphys};

        my $chosenChildRecord;
        my $childRecord;

        foreach $childRecord (@$childrecs) {
            if (!(defined $chosenChildRecord)
                && $childRecord->{timestamp} == $row->{timestamp}
                && !($childRecord->{parentphys} eq $row->{parentphys})) {

                $chosenChildRecord = $childRecord;
            }
        }

        if (defined $chosenChildRecord) {
            $source = $chosenChildRecord->{parentphys};
            $gCfg{dbh}->do("DELETE FROM PhysicalAction WHERE action_id IN ($chosenChildRecord->{action_id})");

            my $sql = <<"EOSQL";
UPDATE
    PhysicalAction
SET
    actiontype = 'MOVE',
    parentphys = ?,
    info = ?
WHERE
    action_id = ?
EOSQL
            my $update;
            $update = $gCfg{dbh}->prepare($sql);

            $update->execute( $target, $source, $row->{action_id});
        } else {
            #the record did not have a matching MOVE_TO. call it a RESTORE
            print "Changing $row->{action_id} to a @{[ACTION_RESTORE]}\n";

            my $sql = <<"EOSQL";
UPDATE
    PhysicalAction
SET
    actiontype = '@{[ACTION_RESTORE]}'
WHERE
    action_id = ?
EOSQL
            my $update;
            $update = $gCfg{dbh}->prepare($sql);

            $update->execute( $row->{action_id});
        }
    }


    # change all remaining MOVE_TO records into MOVE records and swap the src and target
    $sth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalAction '
                               . "WHERE actiontype = '" . ACTION_MOVE_TO . "'");
    $sth->execute();
    $rows = $sth->fetchall_arrayref( {} );

    foreach $row (@$rows) {
        my $update;
        $update = $gCfg{dbh}->prepare('UPDATE PhysicalAction SET '
                                      . 'actiontype = "MOVE", '
                                      . 'parentphys = ?, '
                                      . 'info = ? '
                                      . 'WHERE action_id = ?');
        $update->execute($row->{info}, $row->{parentphys}, $row->{action_id});
    }

    $sth = $gCfg{dbh}->prepare("SELECT * FROM PhysicalAction WHERE actiontype = '" . ACTION_RESTORE . "'");
    $sth->execute();
    $rows = $sth->fetchall_arrayref( {} );

    foreach $row (@$rows) {
        #calculate last name of this file. Store it in $info

        my $sql = "SELECT * FROM PhysicalAction WHERE physname = ? AND timestamp < ? ORDER BY timestamp DESC";

        $sth = $gCfg{dbh}->prepare($sql);
        $sth->execute( $row->{physname}, $row->{timestamp} );

        my $myOlderRecords = $sth->fetchall_arrayref( {} );

        if (scalar @$myOlderRecords > 0) {
            my $update = $gCfg{dbh}->prepare('UPDATE PhysicalAction SET info = ? WHERE action_id = ?');
            $update->execute(@$myOlderRecords[0]->{itemname}, $row->{action_id});
        }
    }

    1;

}  #  End MergeMoveData

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
#  MergeUnpinPinData
###############################################################################
sub MergeUnpinPinData {
    my($sth, $rows, $row, $r, $next_row);
    my $sql = 'SELECT * FROM PhysicalAction ORDER BY timestamp ASC, '
                . 'itemtype ASC, priority ASC, parentdata ASC, sortkey ASC, action_id ASC';
    $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute();

    # need to pull in all recs at once, since we'll be updating/deleting data
    $rows = $sth->fetchall_arrayref( {} );

    return if ($rows == -1);
    return if (@$rows < 2);

    my @delchild = ();

    for $r (0 .. @$rows-2) {
        $row = $rows->[$r];

        if ($row->{actiontype} eq ACTION_PIN && !defined $row->{version}) # UNPIN
        {
            # Search for a matching pin action
            my $u;
            for ($u = $r+1; $u <= @$rows-2; $u++) {
                $next_row = $rows->[$u];

                if (   $next_row->{actiontype} eq ACTION_PIN
                    && defined $next_row->{version}   # PIN
                    && $row->{physname} eq $next_row->{physname}
                    && $row->{parentphys} eq $next_row->{parentphys}
#                    && $next_row->{timestamp} - $row->{timestamp} < 60
#                    && $next_row->{action_id} - $row->{action_id} == 1
                    ) {
                        print "found UNPIN/PIN combination for $row->{parentphys}/$row->{physname}"
                            . "($row->{itemname}) @ ID $row->{action_id}\n"  if $gCfg{verbose};

                        # if we have a unpinFromVersion number copy this one to the PIN handler
                        if (defined $row->{info})
                        {
                            my $sql2 = "UPDATE PhysicalAction SET info = ? WHERE action_id = ?";
                            my $sth2 = $gCfg{dbh}->prepare($sql2);
                            $sth2->execute($row->{info}, $next_row->{action_id});
                        }

                        push (@delchild, $row->{action_id});
                    }

                # if the next action is anything else than a pin stop the search
                $u = @$rows if ($next_row->{actiontype} ne ACTION_PIN );
            }
        }
    }

    if (scalar @delchild > 0) {
        # just numbers here, no need to quote
        my $in_clause = join q{,}, @delchild;
        $gCfg{dbh}->do("DELETE FROM PhysicalAction WHERE action_id IN ($in_clause)");
    }

    1;

}  #  End MergeUnpinPinData

###############################################################################
#  BuildComments
###############################################################################
sub BuildComments {
    my($sth, $rows, $row, $r, $next_row);
    my $sql = "SELECT * FROM PhysicalAction WHERE actiontype='@{[ACTION_PIN]}' AND itemtype=@{[VSS_FILE]} ORDER BY physname ASC";
    $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute();

    # need to pull in all recs at once, since we'll be updating/deleting data
    $rows = $sth->fetchall_arrayref( {} );

    foreach $row (@$rows) {

        # technically we have the following situations:
        # PIN only: we come from the younger version and PIN to a older one: the
        #     younger version is the currenty version of the timestamp of the PIN action
        # UNPIN only: we unpin from a older version to the current version, the
        #     timestamp of the action will again define the younger version
        # UNPIN/PIN with known UNPIN version: we merge from UNPIN version to PIN version
        # UNPIN/PIN with unknown UNPIN version: we are lost in this case and we
        #     can not distinguish this case from the PIN only case.

        my $sql2;
        my $prefix;

        # PIN only
        if (    defined $row->{version}     # PIN version number
            && !defined $row->{info}) {     # no UNPIN version number
            $sql2 = 'SELECT * FROM PhysicalAction'
                    . ' WHERE physname="' . $row->{physname} . '"'
                    . '      AND parentphys ISNULL'
                    . '      AND itemtype=' . VSS_FILE
                    . '      AND version>=' . $row->{version}
                    . '      AND timestamp<=' . $row->{timestamp}
                    . ' ORDER BY version DESC';
            $prefix = "reverted changes for: \n";
        }

        # UNPIN only
        if (   !defined $row->{version}     # no PIN version number
            &&  defined $row->{info}) {     # UNPIN version number
            $sql2 = 'SELECT * FROM PhysicalAction'
                    . ' WHERE physname="' .  $row->{physname} . '"'
                    . '      AND parentphys ISNULL'
                    . '      AND itemtype=' . VSS_FILE
                    . '      AND timestamp<=' . $row->{timestamp}
                    . '      AND version>' . $row->{info}
                    . ' ORDER BY version ASC';
        }

        # UNPIN/PIN
        if (    defined $row->{version}     # PIN version number
            &&  defined $row->{info}) {     # UNPIN version number
            $sql2 = 'SELECT * FROM PhysicalAction'
                    . ' WHERE physname="' . $row->{physname} . '"'
                    . '      AND parentphys ISNULL'
                    . '      AND itemtype=' . VSS_FILE
                    . '      AND version>' . $row->{info}
                    . '      AND version<=' . $row->{version}
                    . ' ORDER BY version ';

            if ($row->{info} > $row->{version}) {
                $sql2 .= "DESC";
                $prefix = "reverted changes for: \n";
            }
            else {
                $sql2 .= "ASC";
            }

        }

        next if !defined $sql2;

        my $sth2 = $gCfg{dbh}->prepare($sql2);
        $sth2->execute();

        my $comments = $sth2->fetchall_arrayref( {} );
        my $comment;
        print "merging comments for $row->{physname}" if $gCfg{verbose};
        print " from $row->{info}" if ($gCfg{verbose} && defined $row->{info});
        print " to $row->{version}" if ($gCfg{verbose} && defined $row->{version});
        print "\n" if $gCfg{verbose};

        foreach my $c(@$comments) {
            print " $c->{version}: $c->{comment}\n" if $gCfg{verbose};
            $comment .= $c->{comment} . "\n";
            $comment =~ s/^\n+//;
            $comment =~ s/\n+$//;
        }

        if (defined $comment && !defined $row->{comment}) {
            $comment = $prefix . $comment if defined $prefix;
            $comment =~ s/"/""/g;
            my $sql3 = 'UPDATE PhysicalAction SET comment="' . $comment . '" WHERE action_id = ' . $row->{action_id};
            my $sth3 = $gCfg{dbh}->prepare($sql3);
            $sth3->execute();
        }
    }
    1;

}  #  End BuildComments

###############################################################################
#  BuildVssActionHistory
###############################################################################
sub BuildVssActionHistory {
    my $vsscache = Vss2Svn::DataCache->new('VssAction', 1)
        || &ThrowError("Could not create cache 'VssAction'");

    my $joincache = Vss2Svn::DataCache->new('SvnRevisionVssAction')
        || &ThrowError("Could not create cache 'SvnRevisionVssAction'");

    my $labelcache = Vss2Svn::DataCache->new('Label')
        || &ThrowError("Could not create cache 'Label'");

    # This will keep track of the current SVN revision, and increment it when
    # the author or comment changes, the timestamps span more than an hour
    # (by default), or the same physical file is affected twice

    my $svnrevs = Vss2Svn::SvnRevHandler->new()
        || &ThrowError("Could not create SVN revision handler");
    $svnrevs->{verbose} = $gCfg{verbose};

    my($sth, $row, $action, $handler, $physinfo, $itempaths, $allitempaths);

    my $sql = 'SELECT * FROM PhysicalAction ORDER BY timestamp ASC, '
            . 'itemtype ASC, priority ASC, parentdata ASC, sortkey ASC, action_id ASC';

    $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute();

ROW:
    while(defined($row = $sth->fetchrow_hashref() )) {
        $action = $row->{actiontype};

        $handler = Vss2Svn::ActionHandler->new($row);
        $handler->{verbose} = $gCfg{verbose};
        $physinfo = $handler->physinfo();

        if (defined($physinfo) && $physinfo->{type} != $row->{itemtype} ) {
            &ThrowWarning("Inconsistent item type for '$row->{physname}'; "
                        . "'$row->{itemtype}' unexpected");
            next ROW;
        }

        $row->{itemname} = Encode::decode_utf8( $row->{itemname} );
        $row->{info} = Encode::decode_utf8( $row->{info} );
        $row->{comment} = Encode::decode_utf8( $row->{comment} );
        $row->{author} = Encode::decode_utf8( $row->{author} );
        $row->{label} = Encode::decode_utf8( $row->{label} );

        # The handler's job is to keep track of physical-to-real name mappings
        # and return the full item paths corresponding to the physical item. In
        # case of a rename, it will return the old name, so we then do another
        # lookup on the new name.

        # Commits and renames can apply to multiple items if that item is
        # shared; since SVN has no notion of such shares, we keep track of
        # those ourself and replicate the functionality using multiple actions.

        if (!$handler->handle($action)) {
            &ThrowWarning($handler->{errmsg})
                if $handler->{errmsg};
            next ROW;
        }

        $itempaths = $handler->{itempaths};

        # In cases of a corrupted share source, the handler may change the
        # action from ACTION_SHARE to ACTION_ADD
        $row->{actiontype} = $handler->{action};

        if (!defined $itempaths) {
            # Couldn't determine name of item
            &ThrowWarning($handler->{errmsg})
                if $handler->{errmsg};

            # If we were adding or modifying a file, commit it to lost+found;
            # otherwise give up on it
            if ($row->{itemtype} == VSS_FILE && ($row->{actiontype} eq ACTION_ADD ||
                $row->{actiontype} eq ACTION_COMMIT)) {

                $itempaths = [undef];
            } else {
                next ROW;
            }
        }

        # we need to check for the next rev number, after all paths that can
        # prematurely call the next row. Otherwise, we get an empty revision.
        $svnrevs->check($row);

        # May contain add'l info for the action depending on type:
        # RENAME: the new name (without path)
        # SHARE: the source path which was shared
        # MOVE: the old path
        # PIN: the path of the version that was pinned
        # LABEL: the name of the label
        $row->{info} = $handler->{info};

        # The version may have changed
        if (defined $handler->{version}) {
            $row->{version} = $handler->{version};
        }

        $allitempaths = join("\t", @$itempaths);
        $row->{itempaths} = $allitempaths;

        $vsscache->add(@$row{ qw(parentphys physname version actiontype itempaths
                             itemtype is_binary info) });
        $joincache->add( $svnrevs->{revnum}, $vsscache->{pkey} );

        if (defined $row->{label}) {
            $labelcache->add(@$row{ qw(physname version label itempaths) });
        }

    }

    $vsscache->commit();
    $svnrevs->commit();
    $joincache->commit();
    $labelcache->commit();

}  #  End BuildVssActionHistory

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
            copy("$gCfg{indeterminateFile}", $physpath);
        }
    } else {
        # It was DESTROYed or DELETEd
        $physpath = "$exportdir/$physname.$version";
        if (! -e $physpath) {
            if (defined $row && defined $row->[0]) {
                copy("$gCfg{destroyedFile}", $physpath);
            } elsif (defined $rowd && defined $rowd->[0]) {
                copy("$gCfg{deletedFile}", $physpath);
            }
        }
    }
    return $physpath;
}

###############################################################################
#  ImportToGit
###############################################################################
sub ImportToGit {

    my($sql, $sth, $action_sth, $row, $revision, $actions, $action, $physname, $itemtype);
    my $repo = Git->repository(Directory => "$gCfg{repo}");
    my %exported = ();

    $sql = 'SELECT * FROM SvnRevision ORDER BY revision_id ASC';

    $sth = $gCfg{dbh}->prepare($sql);
    $sth->execute();

    $sql = <<"EOSQL";
SELECT * FROM
    VssAction
WHERE action_id IN
    (SELECT action_id FROM SvnRevisionVssAction WHERE revision_id = ?)
ORDER BY action_id
EOSQL

    $action_sth = $gCfg{dbh}->prepare($sql);

    $sql = <<"EOSQL";
SELECT MAX(version) FROM
    VssAction
WHERE physname = ?
 AND action_id < ?
EOSQL

    my $rename_sth = $gCfg{dbh}->prepare($sql);

    my $gitrepo = Vss2Svn::GitRepo->new($repo, $gCfg{repo}, $gCfg{author_info});

REVISION:
    while(defined($row = $sth->fetchrow_hashref() )) {

        my $t0 = new Benchmark;

        $revision = $row->{revision_id};
        $gitrepo->begin_revision($row);


        $action_sth->execute($revision);
        $actions = $action_sth->fetchall_arrayref( {} );

ACTION:
        foreach $action(@$actions) {
            $physname = $action->{physname};
            $itemtype = $action->{itemtype};

            my $version = $action->{version};
            if (   !defined $version
                   && (   $action->{action} eq ACTION_ADD
                          || $action->{action} eq ACTION_COMMIT)) {
                &ThrowWarning("'$physname': no version specified for retrieval");

                # fall through and try with version 1.
                $version = 1;
            }

            if ($itemtype == VSS_FILE && defined $version) {
                if ($action->{action} eq ACTION_RENAME) {
                    # version is wrong, step back to the previous action_id version
                    $rename_sth->execute($physname, $action->{action_id});
                    $version = $rename_sth->fetchall_arrayref()->[0][0];
                }
                $exported{$physname} = &ExportVssPhysFile($physname, $version);
            } else {
                $exported{$physname} = undef;
            }

            # do_action needs to know the revision_id, so paste it on
            $action->{revision_id} = $revision;
            $gitrepo->do_action($action, $exported{$physname});
        }
        print "revision $revision: ", timestr(timediff(new Benchmark, $t0)),"\n"
            if $gCfg{timing};

        $gitrepo->commit();
    }

    my @err = @{ $gitrepo->{errors} };

    if (scalar @err > 0) {
        map { &ThrowWarning($_) } @err;
    }

    $gitrepo->finish();

}  #  End ImportToGit

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

For more information on the vss2svn2git project, see:
https://github.com/ldav1s/vss2svn

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

    my($actions, $revisions, $mintime, $maxtime) = &GetStats();

    print <<"EOTXT";
Started at              : $starttime
Ended at                : $endtime
Elapsed time            : $elapsed (H:M:S)

VSS Actions read        : $actions
git commits converted   : $revisions
Date range (YYYY-MM-DD) : $mintime to $maxtime

EOTXT

}  #  End ShowSummary

###############################################################################
#  GetStats
###############################################################################
sub GetStats {
    my($sql, $actions, $revisions, $mintime, $maxtime);

    $sql = <<"EOSQL";
SELECT
    COUNT(*)
FROM
    VssAction
EOSQL

    ($actions) = $gCfg{dbh}->selectrow_array($sql);

    $sql = <<"EOSQL";
SELECT
    COUNT(*)
FROM
    SvnRevision
EOSQL

    ($revisions) = $gCfg{dbh}->selectrow_array($sql);

    $mintime = $gCfg{mintime};
    $maxtime = $gCfg{maxtime};

    foreach($mintime, $maxtime) {
        $_ = POSIX::strftime("%Y-%m-%d", localtime($_));
    }

    # initial creation of the repo wasn't considered an action or revision
    return($actions - 1, $revisions - 1, $mintime, $maxtime);

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
    &CloseAllFiles;

    exit(1);
}  #  End StopConversion

###############################################################################
#  CloseAllFiles
###############################################################################
sub CloseAllFiles {

}  #  End CloseAllFiles

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

    $gCfg{dbh} = DBI->connect("dbi:SQLite2:dbname=$db", '', '',
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

    Vss2Svn::DataCache->SetCacheDir($gCfg{tempdir});
    Vss2Svn::DataCache->SetDbHandle($gCfg{dbh});
    Vss2Svn::DataCache->SetVerbose($gCfg{verbose});

    Vss2Svn::SvnRevHandler->SetRevTimeRange($gCfg{revtimerange});

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

    my $pa_sql = <<"EOSQL";
        physname    VARCHAR,
        version     INTEGER,
        parentphys  VARCHAR,
        actiontype  VARCHAR,
        itemname    VARCHAR,
        itemtype    INTEGER,
        timestamp   INTEGER,
        author      VARCHAR,
        is_binary   INTEGER,
        info        VARCHAR,
        priority    INTEGER,
        sortkey     VARCHAR,
        parentdata  INTEGER,
        label       VARCHAR,
        comment     TEXT
EOSQL

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
        timestamp   ASC,
        priority    ASC,
        sortkey     ASC
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE INDEX
    PhysicalAction_IDX2 ON PhysicalAction (
        physname    ASC,
        parentphys  ASC,
        actiontype  ASC,
        timestamp   ASC,
        author      ASC
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE TABLE
    VssAction (
        action_id   INTEGER PRIMARY KEY,
        parentphys  VARCHAR,
        physname    VARCHAR,
        version     INTEGER,
        action      VARCHAR,
        itempaths   VARCHAR,
        itemtype    INTEGER,
        is_binary   INTEGER,
        info        VARCHAR
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE INDEX
    VssAction_IDX1 ON VssAction (
        action_id   ASC
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE TABLE
    SvnRevision (
        revision_id INTEGER PRIMARY KEY,
        timestamp   INTEGER,
        author      VARCHAR,
        comment     TEXT
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE TABLE
    SvnRevisionVssAction (
        revision_id INTEGER,
        action_id   INTEGER
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE INDEX
    SvnRevisionVssAction_IDX1 ON SvnRevisionVssAction (
        revision_id ASC,
        action_id   ASC
    )
EOSQL

    $gCfg{dbh}->do($sql);

    $sql = <<"EOSQL";
CREATE TABLE
    Label (
        physical VARCHAR,
        version  INTEGER,
        label    VARCHAR,
        imtempaths  VARCHAR
    )
EOSQL

    $gCfg{dbh}->do($sql);

    my @cfgitems = qw(task step vssdir svnurl svnuser svnpwd ssphys tempdir
        setsvndate starttime);

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
    my @statb = stat($gCfg{repo});

    $git_image{Vss2Svn::ActionHandler::VSSDB_ROOT} = $statb[1];
    $image_name{$statb[1]} = $gCfg{repo};

    if (! -d $gCfg{vssdatadir}) {
        die "The VSS database '$gCfg{vssdir}' "
            . "does not appear to be a valid VSS database, as there's no 'data' directory.";
    }

    if (defined($gCfg{author_info}) && ! -r $gCfg{author_info}) {
        die "author_info file '$gCfg{author_info}' is not readable";
    } else {
        open my $info, $gCfg{author_info} or die "Could not open $gCfg{author_info}: $!";

        while(<$info>) {
            my ($username, $author, $author_email) = split(/\t/);
            $author_map->{$username} = { name => $author, email => $author_email };
        }
        close $info;
    }

    $gCfg{sqlitedb} = File::Spec->catfile($gCfg{tempdir}, 'vss_data.db');

    # XML output from ssphysout placed here.
    $gCfg{ssphysout} = File::Spec->catfile($gCfg{tempdir}, 'ssphysout');
    $gCfg{encoding} = ENCODING if !defined($gCfg{encoding});

    # Commit messages for SVN placed here.
    mkdir $gCfg{tempdir} unless (-d $gCfg{tempdir});

    # Directories for holding VSS revisions
    $gCfg{vssdata} = File::Spec->catdir($gCfg{tempdir}, 'vssdata');

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

    &ConfigureXmlParser();

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

    &WriteDestroyedPlaceholderFiles();

    $gCfg{ssphys} ||= 'ssphys';
    $gCfg{svn} ||= 'SVN.exe';

    $gCfg{task} = TASK_INIT;
    $gCfg{step} = 0;
}  #  End Initialize

###############################################################################
#  ConfigureXmlParser
###############################################################################
sub ConfigureXmlParser {

    if(defined($ENV{XML_SIMPLE_PREFERRED_PARSER})) {
        # user has defined a preferred parser; don't mess with it
        $gCfg{xmlParser} = $ENV{XML_SIMPLE_PREFERRED_PARSER};
        return 1;
    }

    $gCfg{xmlParser} = 'XML::Simple';

    eval { require XML::SAX; };

    if($@) {
        # no XML::SAX; let XML::Simple use its own parser
        return 1;
    }
    elsif($gCfg{usingExe}) {
        # Prevent the ParserDetails.ini error message when running from .exe
        XML::SAX->load_parsers($INC[1]);
    }

    $gCfg{xmlParser} = 'XML::SAX::Expat';
    $XML::SAX::ParserPackage = $gCfg{xmlParser};

    my $p;

    eval { $p = XML::SAX::ParserFactory->parser(); };

    if(!$@) {
        # XML::SAX::Expat installed; use it

        # for exe version, XML::Parser::Expat needs help finding its encmaps
        no warnings 'once';

        my $encdir;
        foreach my $dir (@INC) {
            $encdir = "$dir/encodings";
            $encdir =~ s:\\:/:g;
            $encdir =~ s://:/:g;
            if(-d $encdir) {
                print "Adding '$encdir' to encodings file path\n";
                push(@XML::Parser::Expat::Encoding_Path, $encdir);
            }
        }

        return 1;
    }

    undef $XML::SAX::ParserPackage;
    eval { $p = XML::SAX::ParserFactory->parser(); };

    if(!$@) {
        $gCfg{xmlParser} = ref $p;
        return 1;
    }

    # couldn't find a better package; go back to XML::Simple
    $gCfg{'xmlParser'} = 'XML::Simple';
    return 1;

}  #  End ConfigureXmlParser

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
vss2svn2git has determined that this file has been destroyed in VSS history.
vss2svn2git cannot retrieve it, since it no longer exists in the VSS database.
EOTXT
    close(DEST);

    open (DEST, ">$gCfg{deletedFile}");
    print DEST <<"EOTXT";
vss2svn2git has determined that this file has been deleted in VSS history.
vss2svn2git cannot retrieve it, since it no longer exists in the VSS database.
EOTXT
    close(DEST);

    open (DEST, ">$gCfg{indeterminateFile}");
    print DEST <<"EOTXT";
vss2svn2git cannot determine what has happened to this file.
vss2svn2git was not able to retrieve it. This file was possibly lost
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
    my($sth, $rows);
    my ($last_time);
    state $index = 0;

    # We must schedule, since timestamp is not fine enough resolution,
    # that some events happen before they should. So the timeline is
    # fixed here, if possible.


    my ($changeset_count) = $gCfg{dbh}->selectrow_array('SELECT COUNT(*) FROM PhysicalActionChangeset');

    if (defined $changeset_count && $changeset_count > 0) {
        # We have unused data from the last scheduling pass, let's use it.
        $gCfg{dbh}->do('INSERT INTO PhysicalActionSchedule '
                       . 'SELECT * FROM PhysicalActionChangeset');
        $gCfg{dbh}->do('DELETE FROM PhysicalActionChangeset');

        # need to reset time, since there may be two commits in the same timestamp
        ($timestamp) = $gCfg{dbh}->selectrow_array('SELECT timestamp '
                                                   . 'FROM PhysicalActionSchedule '
                                                   . 'WHERE schedule_id = (SELECT MIN(schedule_id) FROM PhysicalActionSchedule)');
    } else {
        # Grab a revisions' worth of PhysicalAction entries and stuff them into PhysicalActionSchedule
        $sth = $gCfg{dbh}->prepare('INSERT INTO PhysicalActionSchedule '
                                   . 'SELECT NULL, * FROM PhysicalAction WHERE timestamp >= ? '
                                   . 'AND timestamp < ? '
                                   . 'ORDER BY timestamp ASC, priority ASC, parentdata DESC');

        $sth->execute($timestamp, $timestamp+$gCfg{revtimerange});
        print "timestamp range: $timestamp - " . ($timestamp+$gCfg{revtimerange}) . "\n";

        $sth = $gCfg{dbh}->prepare('SELECT * FROM PhysicalActionSchedule ORDER BY schedule_id');

        # We may end up here a few times as we schedule
      STARTOVER:
        # deep clone these so we can simulate
        my $giti = dclone(\%git_image);
        my $iname = dclone(\%image_name);
        my $inode_sim = 1; # the stat inode replacement

        # figure out a unique starting inode number for simulation
        my @giti_keys = sort {$b <=> $a} values %{$giti};

        if (scalar @giti_keys > 0) {
            $inode_sim = $giti_keys[0] + 1;
        }

        # start scheduling
        $sth->execute();
        $rows = $sth->fetchall_arrayref( {} );

      ROW:
        foreach my $row (@$rows) {
            if ($index == 0
                && $row->{physname} eq Vss2Svn::ActionHandler::VSSDB_ROOT
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
#                print "out of order: parentphys " . $row->{parentphys} . " physname: " . $row->{physname} . "\n";
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
                        $ooo = $tth->fetchall_arrayref();
                        my @ooo_ids;
                        my @action_ids;

                        foreach my $o (@$ooo) {
                            push @ooo_ids, @{$o}[0];
                            push @action_ids, @{$o}[1];
                        }

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
                                goto STARTOVER;
                            }
                            undef $max_sched;
                        }

#                    print "max sched: $max_sched\n";

                        $tth = $gCfg{dbh}->prepare('SELECT schedule_id, action_id FROM PhysicalActionSchedule '
                                                   . 'WHERE timestamp = ? AND schedule_id > ? '
                                                   . 'ORDER BY schedule_id');
                        $tth->execute($row->{timestamp}, $ooo_ids[0]);
                        $ooo = $tth->fetchall_arrayref();

                        # renumber in order entries
                        my $idx = 0;
                        foreach my $o (@$ooo) {
                            $gCfg{dbh}->do('UPDATE PhysicalActionSchedule SET schedule_id=' . ($ooo_ids[0]+$idx)
                                           . ' WHERE schedule_id = ' . @{$o}[0] . ' AND action_id = ' . @{$o}[1]);
                            ++$idx;
                        }

#                    print "out of order: " . Dumper(\@ooo_ids) . "\n";

                        $tth = $gCfg{dbh}->prepare('SELECT * FROM tmp');
                        $tth->execute();
                        $ooo = $tth->fetchall_arrayref();

#                    print "out of order: " . Dumper($ooo) . "\n";

                        # renumber the out of order entries
                        my $idx2 = 0;
                        foreach my $o (@ooo_ids) {
                            my $j = ($ooo_ids[0]+$idx);
                            print "out of order: $j $o\n";

                            my $rv = $gCfg{dbh}->do("UPDATE tmp SET schedule_id=$j WHERE schedule_id = $o "
                                                    ."AND action_id = " . $action_ids[$idx2]);
#                        print "rv: $rv\n";
                            ++$idx;
                            ++$idx2;
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
                        goto STARTOVER;
                    }
                }

                $parentpath = $iname->{$giti->{$row->{parentphys}}};
                $path = ($row->{itemtype} == VSS_PROJECT)
                    ? File::Spec->catdir($parentpath, $row->{itemname})
                    : File::Spec->catfile($parentpath, $row->{itemname});
            } else {
                # presumably this is a child entry
                # pick a path to update
                if (defined $row->{physname}
                    && defined $giti->{$row->{physname}}
                    && defined $iname->{$giti->{$row->{physname}}}) {
                    $path = @{$iname->{$giti->{$row->{physname}}}}[0];
                    $parentpath = dirname($path);
                }
            }

            &UpdateGitRepository($row, $parentpath, $path, $giti, $iname, \$inode_sim, undef);
        }
        print "done scheduling -- " . (scalar @$rows) . " rows \n";
    }

    &GetOneChangeset($timestamp);
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
    # Again, it's at least two changesets in this case.
    # parentdata = 0 means that there could be comments there.
    ($schedule_id) = $gCfg{dbh}->selectrow_array('SELECT MIN(B.schedule_id) '
                                                 . 'FROM (SELECT comment FROM PhysicalActionSchedule '
                                                 . '      WHERE parentdata = 0 ORDER BY schedule_id LIMIT 1) AS A '
                                                 . 'CROSS JOIN (SELECT schedule_id, comment FROM PhysicalActionSchedule '
                                                 . '            WHERE parentdata = 0) AS B '
                                                 . 'WHERE A.comment != B.comment');
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

    # dump all entries incuding and after the first mismatch of labels
    # Again, it's at least two labels. Even though there are no changes,
    # in a label how we are handling labels makes separating differing
    # labels into a changeset important.
    # parentdata = 0 means that there could be labels there.
    # This should be sufficient to isolate LABEL actions, since other
    # actions won't have label data.
    ($schedule_id) = $gCfg{dbh}->selectrow_array('SELECT MIN(B.schedule_id) '
                                                 . 'FROM (SELECT label FROM PhysicalActionSchedule '
                                                 . '      WHERE parentdata = 0 ORDER BY schedule_id LIMIT 1) AS A '
                                                 . 'CROSS JOIN (SELECT schedule_id, label FROM PhysicalActionSchedule '
                                                 . '            WHERE parentdata = 0) AS B '
                                                 . 'WHERE A.label != B.label');
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

# fake returning inode numbers when simulating
sub StatSimulated {
    my($simulatedref) = @_;
    my @statb = (undef, ++${$simulatedref});

    return @statb;
}

# update the image name mapping when files/directories are moved
sub MoveProject {
    my($oldpath, $newpath, $image_name) = @_;
    my $sep = "/"; # XXX not platform independent
    my $oldpath_re = qr/^\Q${oldpath}${sep}\E(.*)$/;
    my $oldpath_nosep_re = qr/^\Q${oldpath}\E$/;

    foreach my $key (keys %{$image_name}) {
        if (ref($image_name->{$key})) {
            s/$oldpath_re/${newpath}${sep}$1/ for @{$image_name->{$key}};
        } else {
            # have to be a little careful here...
            if ($image_name->{$key} =~ m/$oldpath_re/) {
                $image_name->{$key} =~ s/$oldpath_re/${newpath}${sep}$1/;
            } elsif ($image_name->{$key} =~ m/$oldpath_nosep_re/) {
                $image_name->{$key} = ${newpath};
            }
        }
    }
}

sub RmProject {
    my($path, $git_image, $image_name) = @_;
    my $sep = "/"; # XXX not platform independent
    my $path_re = qr/^\Q${path}${sep}\E/;
    my $path_nosep_re = qr/^\Q${path}\E$/;

    foreach my $key (keys %{$image_name}) {
        if (ref($image_name->{$key})) {
            @{$image_name->{$key}} = grep {!/$path_re/} @{$image_name->{$key}};
            if (scalar @{$image_name->{$key}} == 0) {
                delete $image_name->{$key};
                my @matches = grep { $git_image->{$_} == $key } keys %{$git_image};
                foreach my $m (@matches) {
                    delete $git_image->{$m};
                }
            }
        } elsif ($image_name->{$key} =~ /$path_re|$path_nosep_re/) {
            delete $image_name->{$key};
            my @matches = grep { $git_image->{$_} == $key } keys %{$git_image};
            foreach my $m (@matches) {
                delete $git_image->{$m};
            }
        }
    }
}

# invoke git one action at a time
sub UpdateGitRepository {
    my($row, $parentpath, $path, $git_image, $image_name, $simulatedref, $repo) = @_;

    my @delete_actions = (ACTION_DELETE, ACTION_DESTROY);
    my @restore_actions = (ACTION_RESTORE, ACTION_RESTOREDPROJECT);
    my $simulated = ${$simulatedref};
    my @statb;

    eval {
    for ($row->{itemtype}) {
        when (VSS_PROJECT) {
            for ($row->{actiontype}) {
                when (ACTION_ADD) {
                    if ($simulated) {
                        if (!defined $git_image->{$row->{physname}}) {
                            @statb = StatSimulated($simulatedref);
                            $git_image->{$row->{physname}} = $statb[1];
                            $image_name->{$statb[1]} = $path;
                        }
                    } elsif (! -d $path) {
                        make_path($path);
                        copy($gCfg{keepFile}, $path);
                        @statb = stat($path);
                        $git_image->{$row->{physname}} = $statb[1];
                        $image_name->{$statb[1]} = $path;

                        $repo->command('add', '--',  $path);
                        &RemoveKeep($repo, $parentpath);
                    }
                }
                when (@restore_actions) {
                    # XXX need example
                    # I don't think anything needs to be done here anyway
                    # but I could be mistaken.
                }
                when (ACTION_RENAME) {
                    my $newpath = File::Spec->catdir($parentpath, $row->{info});
                    &DoMoveProject($repo, $path, $newpath, $image_name, $simulated, 1);
                }
                when (ACTION_MOVE_TO) {
                    # physname directory inode to move
                    # parentphys physname's parent directory
                    # info destination directory path
                    my $newpath = File::Spec->catdir($gCfg{repo}, $row->{info});

                    &DoMoveProject($repo, $path, $newpath, $image_name, $simulated, 1);
                }
                when (ACTION_MOVE_FROM) {
                    # physname moved directory inode
                    # parentphys destination's parent directory
                    # info source directory path
                    my $oldpath = File::Spec->catdir($gCfg{repo}, $row->{info});

                    &DoMoveProject($repo, $oldpath, $path, $image_name, $simulated, 0);
                }
                when (@delete_actions) {
                    if ($simulated) {
                        my $s = delete $git_image->{$row->{physname}};
                        delete $image_name->{$s};
                        &RmProject($path, $git_image, $image_name);
                    } elsif (-d $path) {
                        my $s = delete $git_image->{$row->{physname}};
                        delete $image_name->{$s};
                        &RmProject($path, $git_image, $image_name);
                        &GitRm($repo, $parentpath, $path, $row->{itemtype});
                    }
                }
                when (ACTION_RECOVER) {
                    &GitRecover($repo, $row, $path, $git_image, $image_name, $simulatedref);
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
                                @statb = StatSimulated($simulatedref);
                                $git_image->{$row->{physname}} = $statb[1]; # one inode
                                @{$image_name->{$statb[1]}} = ("$path") x 1; # may be on multiple paths
                            }
                        } elsif (! -f $path) {
                            # In the case of a destroyed file there's only the parent record
                            # we'll go ahead and add the file in case the child record is blown away
                            # by something.
                            my ($action_id) = $gCfg{dbh}->selectrow_array("SELECT action_id "
                                                                          . "FROM PhysicalAction "
                                                                          . "WHERE physname = ? AND actiontype = '@{[ACTION_DESTROY]}' "
                                                                          . "LIMIT 1", # just in case
                                                                          undef, $row->{physname});
                            copy((($action_id) ? $gCfg{destroyedFile} : $gCfg{indeterminateFile}), $path); # touch the file
                            $repo->command('add', '--',  $path);
                            &RemoveKeep($repo, $parentpath);
                            @statb = stat($path);

                            $git_image->{$row->{physname}} = $statb[1]; # one inode
                            @{$image_name->{$statb[1]}} = ("$path") x 1; # may be on multiple paths
                        }
                    } elsif (defined $git_image->{$row->{physname}}) {
                        # we have child data here
                        my $s = $git_image->{$row->{physname}};

                        $path = @{$image_name->{$s}}[0];
                        my $exported = &ExportVssPhysFile($row->{physname}, $row->{version});

                        if (defined $exported) {
                            # assuming copy does not change inode number
                            if (!$simulated) {
                                copy(File::Spec->catfile($exported, $row->{physname} . '.' . $row->{version}), $path);
                                $repo->command('add', '--',  $path);
                                &RemoveKeep($repo, $parentpath);
                            }
                        }
                    }
                }
                when (ACTION_RENAME) {
                    # these are only recorded in the parent
                    my $newpath = File::Spec->catfile($parentpath, $row->{info});
                    my $s = $git_image->{$row->{physname}};
                    $repo->command('mv',  $path,  $newpath) if !$simulated;

                    # N.B. inode should _not_ have changed during move
                    @{$image_name->{$s}} = grep {!/^\Q$path\E/} @{$image_name->{$s}};
                    push @{$image_name->{$s}}, $newpath;
                }
                when (@delete_actions) {
                    # these are only recorded in the parent
                    my $path_re = qr/^\Q$path\E/;

                    if ($simulated) {
                        my $s = $git_image->{$row->{physname}};
                        @{$image_name->{$s}} = grep {!/$path_re/} @{$image_name->{$s}};

                        if (scalar @{$image_name->{$s}} == 0) {
                            delete $git_image->{$row->{physname}};
                            delete $image_name->{$s};
                        }
                    } elsif (-f $path) {
                        my $s = $git_image->{$row->{physname}};
                        @{$image_name->{$s}} = grep {!/$path_re/} @{$image_name->{$s}};

                        if (scalar @{$image_name->{$s}} == 0) {
                            delete $git_image->{$row->{physname}};
                            delete $image_name->{$s};
                        }

                        &GitRm($repo, $parentpath, $path, $row->{itemtype});
                    }
                }
                when (ACTION_RECOVER) {
                    &GitRecover($repo, $row, $path, $git_image, $image_name, $simulatedref);
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

                        if (!$simulated) {
                            # XXX assuming copy does not change inode number
                            copy($newver, $path);
                            $repo->command('add', '--',  $path);
                        }
                    }
                }
                when (ACTION_SHARE) {
                    # only recorded in parent (but present in child XML)
                    my $inum = $git_image->{$row->{physname}};
                    my $oldpath = @{$image_name->{$inum}}[0];

                    if ($simulated) {
                        push @{$image_name->{$inum}}, $path;
                    } elsif (! -f $path) {
                        link $oldpath, $path;
                        push @{$image_name->{$inum}}, $path;
                        $repo->command('add', '--',  $path);
                        &RemoveKeep($repo, $parentpath);
                    }
                }
                when (ACTION_BRANCH) {
                    # branches recorded in parent and child
                    # no git action required
                    if ($row->{parentdata}) {
                        # set up bindings for the new branch
                        my $branchtmp = File::Spec->catfile($parentpath, BRANCH_TMP_FILE);
                        copy($path, $branchtmp) if !$simulated; # should create new file
                        if ($simulated) {
                            @statb = StatSimulated($simulatedref);
                        } else {
                            @statb = stat($branchtmp);
                        }
                        $git_image->{$row->{physname}} = $statb[1];
                        @{$image_name->{$statb[1]}} = ("$path") x 1;

                        if (!$simulated) {
                            unlink $path; # decrement any link count
                            move($branchtmp, $path);
                            # shouldn't need to 'git add', it's a file with the same contents
                        }

                        # remove bindings for the old one
                        my $s = $git_image->{$row->{info}};
                        my $path_re = qr/^\Q$path\E/;
                        @{$image_name->{$s}} = grep {!/$path_re/} @{$image_name->{$s}};
                        if (scalar @{$image_name->{$s}} == 0) {
                            delete $git_image->{$row->{info}};
                            delete $image_name->{$s};
                        }
                    }
                }
                when (ACTION_PIN) {
                    my $exported;
                    my $pinfile = $row->{physname} . '.';

                    if (defined $row->{info}) {
                        # this is an unpin

                        # Find the latest version and copy it over...
                        my $qth = $gCfg{dbh}->prepare('SELECT MAX(version) FROM PhysicalAction '
                                                      . 'WHERE physname = ? AND timestamp < ? '
                                                      . 'AND parentphys IS NULL');
                        $qth->execute($row->{physname}, $row->{timestamp});
                        my $ver = $qth->fetchall_arrayref()->[0][0];
                        $exported = &ExportVssPhysFile($row->{physname}, $ver);
                        $pinfile .= $ver;
                    } else {
                        # this is a pin
                        # There's not a really good way to do this, since
                        # git doesn't suport this, nor do most Linux filesystems.
                        # Find the old version and copy it over...
                        $exported = &ExportVssPhysFile($row->{physname}, $row->{version});
                        $pinfile .= $row->{version};
                    }

                    if (defined $exported) {
                        if (!$simulated) {
                            copy(File::Spec->catfile($exported, $pinfile), $path);
                            $repo->command('add', '--',  $path);
                        }
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
        print "image_name: " . Dumper(\%image_name) . "\n";
        print "row: " . Dumper($row) . "\n";
        print "data: " . Dumper($image_name->{$git_image->{$row->{physname}}}) . "\n";
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

    my $tagname = $dlabel;

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

    # Time to gensym
    $tagname = "vss2svn2git_" . $timestamp . "_" . localtime(time);

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
    $ENV{'GIT_AUTHOR_DATE'} = POSIX::strftime("%Y-%m-%dT%H:%M:%S", localtime($timestamp));
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

        if (!defined $label_map->{$row->{label}}) {
            # create a new branch for this label
            $label_map->{$row->{label}} = $tagname;
            $repo->command('checkout', '-q', '--orphan',  $tagname);
            $repo->command('config', "branch." . $tagname . ".description",  $row->{comment}); # give it a description
            $repo->command('reset', '--hard'); # unmark all the "new" files from the commit.
            print "Label `" . $row->{label} . "' is branch `$tagname'.\n";
        } elsif ($branch =~ $master_re) {
            $repo->command('checkout', '-q', $tagname);
        }
        $repo->command('checkout', 'master', '--',  $tmppath);
    }
}

# handle different kinds of moves
sub DoMoveProject {
    my($repo, $path, $newpath, $image_name, $simulated, $newtest) = @_;

    if ($simulated) {
        &MoveProject($path, $newpath, $image_name);
    } elsif ($newtest ? (! -d $newpath) : (-d $path)) {
        $repo->command('mv',  $path,  $newpath);
        # N.B. inode should _not_ have changed during move
        &MoveProject($path, $newpath, $image_name);
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
    my($repo, $row, $path, $git_image, $image_name, $simulatedref) = @_;
    my $simulated = ${$simulatedref};
    my @statb;

    if ($simulated) {
        if (!defined $git_image->{$row->{physname}}) {
            @statb = StatSimulated($simulatedref);
            $git_image->{$row->{physname}} = $statb[1];
            $image_name->{$statb[1]} = $path;
        }
    } elsif (! -e $path) {
        my $rev = $repo->command_oneline('rev-list', '-n', '1', 'HEAD', '--',  $path);
        $repo->command('checkout', "$rev^", '--',  $path);

        @statb = stat($path);
        $git_image->{$row->{physname}} = $statb[1];
        $image_name->{$statb[1]} = $path;
    }
}

sub GitRm {
    my($repo, $parentpath, $path, $itemtype) = @_;

    # add back the keep file before 'git rm', so we don't have to reset
    # inode bookkeeping
    my $keepfile = File::Spec->catfile($parentpath, KEEP_FILE);
    copy($gCfg{keepFile}, $keepfile);

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
