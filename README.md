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
import the data and retarget the output to git at the IMPORTGIT
(IMPORTSVN) stage. The scheduling that was done to get it to SVN was
actually pretty good, but needed a couple of minor fixes.

The import to git is pretty straightforward.

It'll be important to set up the files to be imported using the
.gitattributes and .gitignores in the git repository for crlf
adjustment before starting the import.

This is very experimental right now, and might be kind of broken.
Also it'll only work on Linux for now, because it supports hard links
to emulate "shares".

