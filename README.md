vss2svn2git - Use vss2svn to import a VSS database into git
===========

Fork of @irontoby/vss2svn to import files into a git repository.

Once again, I needed some way of extracting history from an
old VSS 6.0 database, and vss2git didn't do it correctly.  Neither did
the precompiled version of vss2svn, but it did a slightly better
job.  Having contributed to the "legacy" vss2svn as well as the
current vss2svn, I thought it might be better to start with what I
know.

The idea I've come up with is to use ssphys and it's related tools to
import the data. I've actually rewritten the scheduling to work more
on the PhysicalAction stage.  I still probably need to review the
original scheduler to see if I can improve mine.  It still does need
improvement.

Data checks and manipulation are much more SQL intensive now.  I would
like to move to a current version of SQLite.

Also, I've moved to perl 5.10.1 at least for the time being.  The
newer version has a few features that made the switch worthwhile.

It'll be important to set up the files to be imported using the
.gitattributes and .gitignores in the git repository for crlf
adjustment before starting the import.  I still have not tried this.

This is very experimental right now, and might be kind of broken.
Also it'll only work on Linux for now, because it supports hard links
to emulate "shares".

Caveats:

Migration should be performed on a case-insensitive filesystem that is
able to support hard links, such as JFS, ZFS or NTFS.
[ciopfs](http://www.brain-dump.org/projects/ciopfs) might work as
well, but seemed slow when I tried it in comparison with JFS.
Labels will be treated case-insensitively as well, since they will be
stored in the git repository that way.
