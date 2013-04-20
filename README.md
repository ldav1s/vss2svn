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
import the data and retarget the output to git at the IMPORTSVN stage.
I think I'm going to be using mostly the data output by the physical
passes and not so much the later grouping into SVN commits, etc., as
git has the ability to edit history much more flexibly than
subversion.

The git repository as I see it now will be built up using the git
plumbing layer mostly, starting with files, trees, commits, and
tags.

It'll be important to set up the files to be imported using the
.gitattributes in the git repository for crlf adjustment before
starting the import.

This is very experimental right now, and might be kind of broken.
Also it'll only work on Linux for now.

