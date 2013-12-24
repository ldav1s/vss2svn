# vss2svn2git - Use vss2svn to import a Visual SourceSafe database into git

Fork of @irontoby/vss2svn to import files into a git repository.

Once again, I needed some way of extracting history from an
old [Visual SourceSafe](http://msdn.microsoft.com/en-us/library/3h0544kx(VS.80).aspx)
 6.0 database, and [vss2git](http://code.google.com/p/vss2git/)
 didn't do it correctly.  Neither did the precompiled version of
 [vss2svn](http://code.google.com/p/vss2svn/) (which has
 [an official GitHub repository](https://github.com/irontoby/vss2svn/) now,
 but didn't when I started this), but it did a slightly better
job.  Having contributed to the "legacy" vss2svn as well as the
current vss2svn, I thought it might be better to start with what I
know.

The idea I've come up with is to use `ssphys` and it's related tools to
import the data. I've actually rewritten the scheduling to work more
on the earlier stages of `vss2svn`.  I still probably need to review the
original scheduler to see if I can improve mine.  It still does need
improvement.

Data checks and manipulation are much more SQL intensive now.  I've
moved to a more recent version of SQLite as well (SQLite 3).

Also, I've moved to perl 5.10.1 at least for the time being.  The
newer version has a few features that made the switch worthwhile.

It'll be important to set up the files to be imported using the
`.gitattributes` and `.gitignores` in the git repository for crlf
adjustment, etc. before starting the import.  I still have not tried this.

This is very experimental right now, and might be kind of broken.
Also it'll only work on Linux for now, because it supports hard links
to emulate VSS shares.

# Installation

Clone this repo.  Then:

    $ perl Build.PL
    $ ./Build build
    $ sudo ./Build install

or something like that.  You'll need a C++ compiler and Boost 1.53 with
the system and filesytem libraries to build `ssphys`.  For the perl
part `vss2svn2git.pl`, you'll need at least perl 5.10.1, DBI, DBD::SQLite,
XML::LibXML, Git::Repository, Term::ProgressBar, and IPC::Run.

# Migration

It should go without saying, but I'll say it anyway:

__Back up the VSS database and run VSS ANALYZE.EXE on it prior to
running vss2svn2git on the database.__

Migration should be performed on a case-insensitive, case-preserving
filesystem that is able to support hard links, such as JFS, ZFS or NTFS.
You might be able to use a standard case-sensitive filesystem
(e.g. ext4), but I have not tried it.  It could work, since VSS is
supposed to be case-insensitive, case-preserving as well.

This filesystem needs to have enough space, since at least 2 copies of
the VSS database will be extracted out onto it (the `--repo` directory
itself and the `--tempdir` work directory with extracted files). The
directory for `--repo` and `--tempdir` _must_ be on the same
filesystem for hard links.

so something like (say for an 8GiB JFS filesystem):

    $ fallocate -l 8G migrate.img
    $ mkfs.jfs -O migrate.img
    $ sudo losetup -l /dev/loop0 /path/to/migrate.img
    $ sudo mount -t jfs /dev/loop0 /mnt
    $ cd /mnt
    $ vss2svn.pl --vssdir /path/to/some/vss --author_info /path/to/vss_authors.txt

## After the migration

All the files that are VSS shares at the end of VSS history are
documented in the `--repo` directory in `.git/hooks/post-merge`.  I
just followed the suggestion of
 [one Stack Overflow user](http://stackoverflow.com/a/9322283/425738)
 who apparently uses this technique to have persistent hard linked
 files in his local repository.  I have no experience with it.  This
 file can be safely removed if you don't want VSS shares anymore.

I'd recommend performing a `git gc` of the repository.  If you don't
want the VSS shares, I'd also recommend a `git clone` of the
repository to make sure all the hard links are broken.

## How it works

Data extraction is performed in much the same way as vss2svn:

* The VSS database is read by `ssphys` and compiled into the SQLite
  database (the 'LOADVSSNAMES', 'FINDDBFILES', and 'GETPHYSHIST'
  stages).
* Eliminates `~sak*` files inserted by Visual Studio ('REMOVETMPCHECKIN').
* Normalizes data between parents and children ('FIXUPPARENT') and
  performs other fixes for scheduling.
* Tests to make sure that all VSS users have a corresponding git author
  ('TESTGITAUTHORINFO').
* Schedules the actions in the SQLite database and performs the
  corresponding git actions on the repository for all history actions,
  except labels ('GITREAD') .
* Creates an orphaned branch for each label, and copies the specified
  files/projects into the branch ('GITLABEL').
* Final cleanup ('CLEANUP').

Each file in the git repository is hard linked to a file in the
vss2svn2git work directory, named as the corresponding VSS database
unit for the file.  This link file acts as the 'head' or 'tip'
revision of the file and any changes are applied to the link file
rather than any files in the git repository.  Pinned files are also
hard linked to a link file with a specific version number appended to
it.  This allows for a very easy implementation of VSS shared files.

What this means is that git attributes are not going to be as flexible
as they usually are when dealing with VSS shared files.  For example
if the shared `foo/foo.txt` and `bar/foo.txt` have different
incompatible attributes in `.gitattributes`:

    foo/foo.txt -text
    bar/foo.txt text

It'll be hard to say exactly _which_ attribute will be applied since
they are the same file.  This should not be a problem most of the time.

I'm treating the destroyed files as deleted files mostly.  It seems to
me that VSS's destroy option was primarily a _storage saving
mechanism_ when disk space was scarcer and not an _information removal
mechanism_ even though it did do that as well.  I'm using
`.git/info/exclude` to filter out files that are destroyed.

