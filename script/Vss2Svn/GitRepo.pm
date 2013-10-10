package Vss2Svn::GitRepo;

use warnings;
use strict;

use Git;
use Hash::Case::Preserve;
use POSIX;
use File::Basename;
use File::Copy;
use File::Find;
use File::Spec;
use File::Path qw(make_path remove_tree);

use constant ISO8601_FMT => "%Y-%m-%dT%H:%M:%S";
use constant KEEP_FILE => ".vss2svn2gitkeep";
use constant SHARE_TEMP_FILE => ".vss2svn2gitshare";

our %gHandlers =
    (
     ADD        => \&_add_handler,
     COMMIT     => \&_commit_handler,
     RENAME     => \&_rename_handler,
     SHARE      => \&_share_handler,
     BRANCH     => \&_branch_handler,
     MOVE       => \&_move_handler,
     DELETE     => \&_delete_handler,
     DESTROY     => \&_delete_handler,
     RECOVER    => \&_recover_handler,
     PIN        => \&_pin_handler,
     LABEL      => \&_label_handler,
    );

###############################################################################
#  new
###############################################################################
sub new {
    my($class, $repo, $repodir, $author_info_file) = @_;

    my $self =
        {
         repo => $repo,
         repodir => $repodir,
         revision => 0,
         errors => [],
         username => '',
         author_date => '',
         author_timestamp => '',
         author_map => {},
         label_map => {},
         comment => '',
         file_shares => [],
         file_shares_rev => [],
         on_master_branch => 1,
        };

    tie(%{$self->{author_map}}, 'Hash::Case::Preserve');
    open my $info, $author_info_file or die "Could not open $author_info_file: $!";

    while(<$info>) {
        my ($username, $author, $author_email) = split(/\t/);
        $self->{author_map}->{$username} = { name => $author, email => $author_email };
    }
    close $info;

    $self = bless($self, $class);
    return $self;

}  #  End new

###############################################################################
#  commit
###############################################################################
sub commit {
    my($self) = @_;

    $self->_git_setenv();
    $self->{repo}->command('commit', '-a', '--allow-empty-message', '--no-edit', '-m',  $self->{comment});

    if (!$self->{on_master_branch}) {
        # back to master
        $self->{repo}->command('checkout', '-q', 'master');
        $self->{on_master_branch} = 1;
    }

}  #  End finish

###############################################################################
#  finish
###############################################################################
sub finish {
    my($self) = @_;

    my @shares = ();
    # document our hard links for 'git pull'
    # Found this at a response to a question on how to handle hard links with git
    # at Stack Overflow <http://stackoverflow.com/questions/3729278/git-and-hard-links>.
    # The response given by Niloct <http://stackoverflow.com/users/152016/niloct>
    # here <http://stackoverflow.com/a/9322283/425738> is what I based this code on.
    # Neither Stack Overflow nor Niloct endorses me or my use of their work.
    # SO is CC BY-SA 3.0 <http://creativecommons.org/licenses/by-sa/3.0/>
    # at the time of this writing.
    foreach my $key (sort keys $self->{file_shares}) {
        my $ary = $self->{file_shares}->{$key};
        my @keydir = File::Spec->splitdir($key);

        unshift @keydir, File::Spec->updir();
        unshift @keydir, '$GIT_DIR';

        my $keypath = File::Spec->catfile(@keydir);

        # synthesize the hard link
        foreach my $e (@$ary) {
            my @edir = File::Spec->splitdir($e);
            unshift @edir, File::Spec->updir();
            unshift @edir, '$GIT_DIR';

            my $linkpath = File::Spec->catfile(@edir);
            my $link = 'ln -f ' . $keypath . ' ' . $linkpath;
            push @shares, $link;
        }
    }

    if (scalar @shares > 0) {
        my $file = File::Spec->catfile($self->{repodir}, '.git', 'hooks', 'post-merge');
        open FILE, ">$file";
        print FILE "#!/bin/sh\n";
        foreach my $s (@shares) {
            print FILE "$s\n";
        }
        close FILE;
        chmod 0755, $file;
    }

}  #  End finish

###############################################################################
#  begin_revision
###############################################################################
sub begin_revision {
    my($self, $data) = @_;
    my($revision, $author, $timestamp, $comment) =
        @{ $data }{qw(revision_id author timestamp comment)};

    $self->{username} = $author;
    $self->{comment} = $comment;
    $self->{author_timestamp} = $timestamp;
    $self->{author_date} = $self->git_timestamp($self->{author_timestamp});
    $self->{revision} = $revision;

}  #  End begin_revision

###############################################################################
#  do_action
###############################################################################
sub do_action {
    my($self, $data, $expdir) = @_;

    my $action = $data->{action};

    my($handler, $this_action);

    foreach my $itempath (split "\t", $data->{itempaths}) {
        $this_action = $action;

        $handler = $gHandlers{$this_action};

        $self->$handler($itempath, $data, $expdir);
    }


}  #  End do_action

sub _create_keep {
    my($self, $keepdir) = @_;

    # touch a file, and add it to keep directory
    my $keep = File::Spec->catfile($keepdir, KEEP_FILE);
    open FILE, ">$keep";
    close FILE;
    $self->{repo}->command('add', '--',  $keep);
}

sub _remove_keep {
    my($self, $keepdir) = @_;

    # There's now a file in $keepdir, remove any keep file
    my $keep = File::Spec->catfile($keepdir, KEEP_FILE);

    if (-f $keep) {
        $self->{repo}->command('rm', '-f', '-q', '--',  $keep);
    }
}

###############################################################################
#  _add_handler
###############################################################################
sub _add_handler {
    my($self, $itempath, $data, $expdir) = @_;

    my ($tmppath, $tmpdir, $expfile);
    my @itemdir = $self->_append_repodir($itempath);
    if ($data->{itemtype} == 2
        && -f ($tmppath = File::Spec->catfile(@itemdir))) {
        $self->add_error("Attempt to re-add file '$itempath' at "
                         . "revision $data->{revision_id}, "
                         . "changing to modify; possibly missing delete");
        return $self->_commit_handler ($itempath, $data, $expdir);
    } elsif (-d ($tmppath = File::Spec->catdir(@itemdir)) && !($itempath eq "/")) {
        # creating a new VSS database can cause a "ADD" for a "/" item
        # which will fail.
        $self->add_error("Attempt to re-add directory '$itempath' at "
                         . "revision $data->{revision_id},"
                         . " skipping action: possibly missing delete");
        return 0;
    }

    if (! -d ($tmpdir = dirname($tmppath))) {
        if (!($itempath =~ m/^\/orphaned\/_.*/)) {
	    $self->add_error("Parent path missing while trying to add "
                             . "item '$itempath' at "
                             . "revision $data->{revision_id}: "
                             . "adding missing "
                             . "parents");
	}
        $self->_make_path($tmpdir);
    }

    if ($data->{itemtype} == 2
        && defined ($expfile = $self->get_export_file($data, $expdir))) {

        copy($expfile, $tmppath);
        $self->{repo}->command('add', '--',  $tmppath);
        $self->_remove_keep($tmpdir);
    } elsif ($data->{itemtype} == 1) {
        $self->_make_path($tmppath);
    }

}  #  End _add_handler

###############################################################################
#  _commit_handler
###############################################################################
sub _commit_handler {
    my($self, $itempath, $data, $expdir) = @_;

    my ($tmppath, $expfile);
    my @itemdir = $self->_append_repodir($itempath);
    if (! -f ($tmppath = File::Spec->catfile(@itemdir))) {
        $self->add_error("Attempt to commit to non-existent file "
                         . "'$itempath' at "
                         . "revision $data->{revision_id}, changing to add; "
                         . "possibly missing recover");
        return $self->_add_handler ($itempath, $data, $expdir);
    }

    if ($data->{itemtype} == 2
        && defined ($expfile = $self->get_export_file($data, $expdir))) {

        # update the file
        copy($expfile, $tmppath);
        $self->{repo}->command('add', '--',  $tmppath);
    }
}  #  End _commit_handler

###############################################################################
#  _rename_handler
###############################################################################
sub _rename_handler {
    my($self, $itempath, $data, $expdir) = @_;

    # to rename a file in SVN, we must add "with history" then delete the orig.

    my $newname = $data->{info};
    my $newpath = $itempath;
    my $tmpnewpath;
    my $tmpoldpath;
    my $tmppath;
    my @itemdir = $self->_append_repodir($itempath);
    my @newdir;

    if ($data->{itemtype} == 1) {
        $newpath =~ s:(.*/)?.+$:$1$newname:;
        @newdir = $self->_append_repodir($newpath);
        $tmpoldpath = File::Spec->catdir(@itemdir);
        $tmpnewpath = File::Spec->catdir(@newdir);
    } else {
        $newpath =~ s:(.*/)?.*:$1$newname:;
        @newdir = $self->_append_repodir($newpath);
        $tmpoldpath = File::Spec->catfile(@itemdir);
        $tmpnewpath = File::Spec->catfile(@newdir);
    }

    if (-e $tmpnewpath) {
        $self->add_error("Attempt to rename item '$itempath' to '$newpath' at "
                         . "revision $data->{revision_id}, but destination "
                         . "already exists: possibly missing delete; skipping");
        return 0;
    }

    if (! -e $tmpoldpath) {
        $self->add_error("Attempt to rename item '$itempath' to '$newpath' at "
                         . "revision $data->{revision_id}, but source "
                         . "doesn't exist: possibly missing recover; skipping");
        return 0;
    }

    if (! -d ($tmppath = dirname($tmpnewpath))) {
        $self->add_error("Parent path missing while trying to rename "
                         . "item '$itempath' to '$newpath' at "
                         . "revision $data->{revision_id}: adding missing parents");
        $self->_make_path($tmppath);
    }

    $self->{repo}->command('mv',  $tmpoldpath,  $tmpnewpath);

    $self->_update_file_shares($itempath, $newpath);
}  #  End _rename_handler

###############################################################################
#  _share_handler
###############################################################################
sub _share_file {
    my($self, $itempath, $info, $newpath) = @_;

    # hard link to the destination. Great.
    my @infodir = $self->_append_repodir($info);
    my $link = File::Spec->catfile(@infodir);
    link($link, $newpath);
    $self->{repo}->command('add', '--',  $newpath);

    # We'll track this instead of writing it to file just now,
    # in case it gets removed by a BRANCH we haven't read yet.
    if (!defined $self->{file_shares}->{$info}) {
        $self->{file_shares}->{$info} = ();
    }
    push @$self->{file_shares}->{$info}, $itempath;

    $self->_remove_keep(dirname($newpath));

    $self->{file_shares_rev}->{$itempath} = $info;
}

###############################################################################
#  _share_handler
###############################################################################
sub _share_handler {
    my($self, $itempath, $data, $expdir) = @_;

    my ($tmppath, $tmpdir);
    my @itemdir = $self->_append_repodir($itempath);
    if (($data->{itemtype} == 2
         && -e ($tmppath = File::Spec->catfile(@itemdir)))
        || ($data->{itemtype} == 1
            && -e ($tmppath = File::Spec->catdir(@itemdir)))) {
        $self->add_error("Attempt to share item '$data->{info}' to '$itempath' "
                         . "at revision $data->{revision_id}, "
                         . "but destination "
                         . "already exists: possibly missing delete; skipping");
        return 0;
    }

    if (! -d ($tmpdir = dirname($tmppath))) {
        $self->_make_path($tmpdir);
    }

    if ($data->{itemtype} == 1) {
        # We effectively have a new project here
        # Must traverse the old location and share files here
        my @infodir = $self->_append_repodir($data->{info});
        my $olddir = File::Spec->catdir(@infodir);

        $self->_make_path($tmppath);

        find({
            preprocess => sub {
                return sort grep {!/^(\.|\.\.)$/} @_;
            },
            wanted => sub {
                if (-d $_) {
                    my $newp = File::Spec->catdir($tmppath, $File::Find::name);
                    $self->_make_path($newp);
                } else {
                    my @nitempdir = File::Spec->splitdir($itempath);
                    push @nitempdir, $File::Find::name;
                    my $nitemp = File::Spec->catfile(@nitempdir);
                    my @ninfodir = File::Spec->splitdir($data->{info});
                    push @ninfodir, $File::Find::name;
                    my $ninfo = File::Spec->catfile(@ninfodir);
                    my $nname = File::Spec->catfile($tmppath,
                                                    $File::Find::name);
                    $self->_share_file($nitemp, $ninfo, $nname);
                }
            },
         }, $olddir);

    } else {
        $self->_share_file($itempath, $data->{info}, $tmppath);
    }

}  #  End _share_handler

sub _break_share_link {
    my($self, $dinfo) = @_;

    my $sdir = dirname($dinfo);
    my $stemp = File::Spec->catfile($sdir, SHARE_TEMP_FILE);

    # copy to a temp file
    copy($dinfo, $stemp);
    # break the share link
    unlink $dinfo;
    # move back
    move($stemp, $dinfo);

    # Remove the share link from tracking
    $self->_update_file_shares(undef, $dinfo);
}

###############################################################################
#  _branch_handler
###############################################################################
sub _branch_handler {
    my($self, $itempath, $data, $expdir) = @_;

    if (defined $data->{info}) {
        if ($data->{itemtype} == 1) {
            find({
                preprocess => sub {
                    return sort grep {!/^(\.|\.\.)$/} @_;
                },
                wanted => sub {
                    if (-f $_) {
                        my @ninfodir = File::Spec->splitdir($data->{info});
                        push @ninfodir, $File::Find::name;
                        my $ninfo = File::Spec->catfile(@ninfodir);
                        $self->_break_share_link($ninfo);
                    }
                },
                 }, $data->{info});
        } else {
            $self->_break_share_link($data->{info});
        }
    }

}  #  End _branch_handler

###############################################################################
#  _move_handler
###############################################################################
sub _move_handler {
    my($self, $itempath, $data, $expdir) = @_;

    my $oldpath = $data->{info};
    my $tmpnewpath;
    my $tmpoldpath;
    my $tmppath;
    my @itemdir = $self->_append_repodir($itempath);
    my @infodir = $self->_append_repodir($data->{info});

    if ($data->{itemtype} == 1) {
        $tmpoldpath = File::Spec->catdir(@infodir);
        $tmpnewpath = File::Spec->catdir(@itemdir);
    } else {
        $tmpoldpath = File::Spec->catfile(@infodir);
        $tmpnewpath = File::Spec->catfile(@itemdir);
    }

    if (-e $tmpnewpath) {
        $self->add_error("Attempt to move item '$oldpath' to '$itempath' "
                         . "at revision $data->{revision_id}, "
                         . "but destination already exists: "
                         . "possibly missing delete; skipping");
        return 0;
    }

    if (! -e $tmpoldpath) {
        $self->add_error("Attempt to move item '$oldpath' to '$itempath' "
                         . "at revision $data->{revision_id}, "
                         . "but source doesn't exists: possibly "
                         . "missing recover; skipping");
        return 0;
    }

    if (! -d ($tmppath = dirname($tmpnewpath))) {
        $self->add_error("Parent path missing while trying to move "
                         . "item '$oldpath' to '$itempath' at "
                         . "revision $data->{revision_id}: adding missing parents");
        $self->_make_path($tmppath);
    }

    $self->{repo}->command('mv',  $tmpoldpath,  $tmpnewpath);
    $self->_update_file_shares($oldpath, $itempath);

}  #  End _move_handler

###############################################################################
#  _delete_handler
###############################################################################
sub _delete_handler {
    my($self, $itempath, $data, $expdir) = @_;

    my $tmppath;
    my $parent;
    my @itemdir = $self->_append_repodir($itempath);
    if ($data->{itemtype} == 1) {
        $tmppath = File::Spec->catdir(@itemdir);
    } else {
        $tmppath = File::Spec->catfile(@itemdir);
    }

    if (! -e $tmppath) {
        $self->add_error("Attempt to delete non-existent item '$itempath' "
                         . "at revision $data->{revision_id}: "
                         . "possibly missing recover/add/share; skipping");
        return 0;
    }

    # git will remove the directory if the last file in the
    # directory is removed.
    $parent = dirname($tmppath);
    $self->{repo}->command('rm', '-rf', '-q', '--',  $tmppath);
    $self->_update_file_shares($itempath, undef);

    if (! -e $parent) {
        # got nuked by rm
        make_path($parent);
    }

    # add back any needed keep files
    $self->_add_keep_files($parent);
}  #  End _delete_handler

###############################################################################
#  _recover_handler
###############################################################################
sub _recover_handler {
    my($self, $itempath, $data, $expdir) = @_;

    my $tmppath;
    my @itemdir = $self->_append_repodir($itempath);
    if (($data->{itemtype} == 2
         && -e ($tmppath = File::Spec->catfile(@itemdir)))
        || ($data->{itemtype} == 1
            && -e ($tmppath = File::Spec->catdir(@itemdir)))) {

        $self->add_error("Attempt to recover existing item '$itempath' at "
                         . "revision $data->{revision_id}: possibly "
                         . "missing delete; change to commit");
        return $self->_commit_handler ($itempath, $data, $expdir);
    }

    # find the most recent one and recover it
    my $rev = $self->{repo}->command_oneline('rev-list', '-n', '1', 'HEAD', '--',  $tmppath);
    $self->{repo}->command('checkout', "$rev^", '--',  $tmppath);
}  #  End _recover_handler

###############################################################################
#  _pin_handler
###############################################################################
sub _pin_handler {
    my($self, $itempath, $data, $expdir) = @_;

    my $tmppath;
    my @itemdir = $self->_append_repodir($itempath);
    if (($data->{itemtype} == 2
         && ! -e ($tmppath = File::Spec->catfile(@itemdir)))
        || ($data->{itemtype} == 1
            && ! -e ($tmppath = File::Spec->catdir(@itemdir)))) {
        $self->add_error("Attempt to pin non-existing item '$itempath' at "
                         . "revision $data->{revision_id}: possibly "
                         . "missing recover; skipping");
        return 0;
    }

    # XXX: should check this
    my @revs = $self->{repo}->command('rev-list', '--reverse', 'HEAD', '--',  $tmppath);
    my $ver = $revs[$data->{version}-1];
    $self->{repo}->command('checkout', "$ver^", '--',  $tmppath);
}  #  End _pin_handler

sub _get_valid_ref_name {
    my($self, $dinfo) = @_;

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

    my $tagname = $dinfo;

    if (defined $self->{label_map}->{$dinfo}) {
        $tagname = $self->{label_map}->{$dinfo};
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
    $tagname = "vss2svn2git_" . $self->{author_timestamp} . "_" . localtime();

  DONE:

    return $tagname;
}

###############################################################################
#  _label_handler
###############################################################################
sub _label_handler {
    my($self, $itempath, $data, $expdir) = @_;

    # This one's a little tricky for git.
    # With git, there's no way to constrain a branch or tag to just a subset of
    # the repository.  So we'll create an orphan branch and dump files into it.
    # The revision that contains a label should only contain other related labels,
    # if any.

    my $tmppath;
    my @itemdir = $self->_append_repodir($itempath);
    if ($self->{on_master_branch}
        && ((($data->{itemtype} == 2
              && ! -e ($tmppath = File::Spec->catfile(@itemdir)))
             || ($data->{itemtype} == 1
                 && ! -e ($tmppath = File::Spec->catdir(@itemdir)))))) {
        $self->add_error("Attempt to label non-existing item '$itempath' at "
                         . "revision $data->{revision_id}: possibly "
                         . "missing recover; skipping");
        return 0;
    }

    my $tagname = $self->_get_valid_ref_name($data->{info});
    my @tagnamedir = File::Spec->splitdir($itempath);
    shift @tagnamedir; # remove leading '/'

    # "git checkout master" is hampered by absolute paths in this case
    if ($data->{itemtype} == 2) {
        $tmppath = File::Spec->catfile(@tagnamedir);
    } else {
        $tmppath = File::Spec->catdir(@tagnamedir);
    }

    # switch to the label branch
    if (!defined $self->{label_map}->{$data->{info}}) {
        # create a new branch for this label
        $self->{label_map}->{$data->{info}} = $tagname;
        $self->{repo}->command('checkout', '-q', '--orphan',  $tagname);
        $self->{repo}->command('config', "branch." . $tagname . ".description",  $self->{comment}); # give it a description
        $self->{repo}->command('reset', '--hard'); # unmark all the "new" files from the commit.
        print "Label `" . $data->{info} . "' is branch `$tagname'.\n";
    } elsif ($self->{on_master_branch}) {
        $self->{repo}->command('checkout', '-q', $tagname);
    }
    $self->{on_master_branch} = 0;

    # copy stuff from master
    $self->{repo}->command('checkout', 'master', '--',  $tmppath);

}  #  End _label_handler

###############################################################################
#  get_export_file
###############################################################################
sub get_export_file {
    my($self, $data, $expdir) = @_;

    if (!defined($expdir)) {
        return undef;
    } elsif (!defined($data->{version})) {
        $self->add_error(
            "Attempt to retrieve file contents with unknown version number");
        return undef;
    }
    my @expdirdir = File::Spec->splitdir($expdir);
    push @expdirdir, "$data->{physname}.$data->{version}";
    my $file = File::Spec->catfile(@expdirdir);

    return $file;
}  #  End get_export_file

###############################################################################
#  git_timestamp
###############################################################################
sub git_timestamp {
    my($self, $vss_timestamp) = @_;

    # set the correct time: VSS stores the local time as the timestamp
    # Assuming that the TZ in the VSS database is the TZ we are now using.
    return POSIX::strftime(ISO8601_FMT, localtime($vss_timestamp));

}  #  End git_timestamp


###############################################################################
#  add_error
###############################################################################
sub add_error {
    my($self, $msg) = @_;

    push @{ $self->{errors} }, $msg;
}  #  End add_error

###############################################################################
#  _update_file_shares
###############################################################################
sub _update_file_shares {
    my($self, $oldpath, $newpath) = @_;

    if (defined $oldpath && defined $newpath) {
        # move or rename

        foreach my $key (keys $self->{file_shares}) {
            if ($key =~ m/^\Q$oldpath\E/) {
                my $ary = $self->{file_shares}->{$key};
                undef $self->{file_shares}->{$key};

                $key =~ s/^\Q$oldpath\E/\Q$newpath\E/;
                $self->{file_shares}->{$key} = $ary;

                foreach my $e (@$ary) {
                    $self->{file_shares_rev}->{$e} = $key;
                }
            }
        }

        foreach my $key (keys $self->{file_shares_rev}) {
            if ($key =~ m/^\Q$oldpath\E/) {
                my $info = $self->{file_shares_rev}->{$key};
                undef $self->{file_shares_rev}->{$key};

                $key =~ s/^\Q$oldpath\E/\Q$newpath\E/;
                $self->{file_shares_rev}->{$key} = $info;

                my @ary = ();
                foreach my $e (@$self->{file_shares}->{$info}) {
                    $e =~ s/^\Q$oldpath\E/\Q$newpath\E/;
                    push @ary, $e;
                }
                $self->{file_shares}->{$info} = @ary;
            }
        }
    } elsif (defined $oldpath && !defined $newpath) {
        # delete

        foreach my $key (keys $self->{file_shares}) {
            if ($key =~ m/^\Q$oldpath\E/) {
                my $ary = $self->{file_shares}->{$key};
                undef $self->{file_shares}->{$key};

                foreach my $e (@$ary) {
                    undef $self->{file_shares_rev}->{$e};
                }

                my $share = pop @$ary;

                if (defined $share) {
                    $self->{file_shares}->{$share} = $ary;
                    foreach my $e (@$ary) {
                        $self->{file_shares_rev}->{$e} = $share;
                    }
                }
            }
        }
    } elsif (!defined $oldpath && defined $newpath) {
        # branch
        my $info = $self->{file_shares_rev}->{$newpath};
        undef $self->{file_shares_rev}->{$newpath};

        my $ary = $self->{file_shares}->{$info};
        $self->{file_shares}->{$info} = grep ! /^\Q$info\E/, @$ary;
    }
}

sub _git_setenv {
    my($self) = @_;
    my $map = $self->{author_map}->{$self->{username}};

    $ENV{'GIT_AUTHOR_NAME'} = $map->{name};
    $ENV{'GIT_AUTHOR_EMAIL'} = $map->{email};
    $ENV{'GIT_AUTHOR_DATE'} = $self->{author_date};
}

sub _append_repodir {
    my($self, $path) = @_;

    my @pathdir = File::Spec->splitdir($path);
    unshift @pathdir, $self->{repodir};

    return @pathdir;
}

sub _add_keep_files {
    my($self, $path) = @_;

    if (-d $path) {
        # This ensures that directories will have keep files
        # even though their contents might have been emptied.
        opendir(my $dh, $path);
        my $dircnt = scalar(grep {!/^(\.|\.\.)$/} readdir($dh));
        closedir $dh;

        if ($dircnt == 0) {
            $self->_create_keep($path);
        } else {
            find({
                preprocess => sub {
                    return sort grep {!/^(\.|\.\.)$/} @_;
                },
                wanted => sub {
                    if (-d $_) {
                        opendir(my $dh, $_);
                        my $dircnt = scalar(grep {!/^(\.|\.\.)$/} readdir($dh));
                        closedir $dh;

                        if ($dircnt == 0) {
                            $self->_create_keep($File::Find::name);
                        }
                    }
                },
                 }, $path);
        }
    }
}

sub _make_path {
    my($self, $path) = @_;
    my $tmppath;
    my @paths = File::Spec->splitdir($path);
    my ($len, $tmplen);

    for ($len = 0; $len < scalar @paths; ++$len) {
        my @tmppaths = ();

        for ($tmplen = 0; $tmplen < $len+1; ++$tmplen) {
            push @tmppaths, $paths[$tmplen];
        }
        $tmppath = File::Spec->catdir(@tmppaths);

        if (! -e $tmppath && ! -d $tmppath) {
            make_path($tmppath);
            $self->_create_keep($tmppath);
        }
    }

}

1;
