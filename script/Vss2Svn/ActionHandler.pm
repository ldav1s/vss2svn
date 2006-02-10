package Vss2Svn::ActionHandler;

use warnings;
use strict;

our %handlers =
    (
     ADD        => \&_add_handler,
     COMMIT     => \&_commit_handler,
     RENAME     => \&_rename_handler,
     SHARE      => \&_share_handler,
     BRANCH     => \&_branch_handler,
     MOVE       => \&_move_handler,
     DELETE     => \&_delete_handler,
     RECOVER    => \&_recover_handler,
    );

our(%gPhysInfo);

###############################################################################
#  new
###############################################################################
sub new {
    my($class, $row) = @_;

    my $self =
        {
         row => $row,
         info => undef,
         errmsg => undef,
         itempaths => undef,
         recursed => 0,
         physname_seen => '',
        };

    return bless($self, $class);
}  #  End new

###############################################################################
#  handle
###############################################################################
sub handle {
    my($self, $action) = @_;

    my $handler = $handlers{$action};

    if (!defined($handler)) {
        $self->{errmsg} = "Unknown action '$action'";
        return 0;
    }

    return $self->$handler;

}  #  End handle

###############################################################################
#  physinfo
###############################################################################
sub physinfo {
    my($self) = @_;

    return $gPhysInfo{ $self->{row}->{physname} };
}  #  End physinfo

###############################################################################
#  _add_handler
###############################################################################
sub _add_handler {
    my($self) = @_;
    my $row = $self->{row};

    # For each physical item, we store its "real" physical parent in the
    # 'parentphys' property, then keep a list of additional shared parents in
    # the 'sharedphys' array.

    $gPhysInfo{ $row->{physname} } =
        {
         type       => $row->{itemtype},
         name       => $row->{itemname},
         parentphys => $row->{parentphys},
         sharedphys => [],
        };

    # File was just created so no need to look for shares
    $self->{itempaths} = $self->_get_current_item_paths(1);

    return 1;

}  #  End _add_handler

###############################################################################
#  _commit_handler
###############################################################################
sub _commit_handler {
    my($self) = @_;
    my $row = $self->{row};

    $self->{itempaths} = $self->_get_current_item_paths();

}  #  End _commit_handler

###############################################################################
#  _rename_handler
###############################################################################
sub _rename_handler {
    my($self) = @_;
    my $row = $self->{row};

    # Get the existing paths before the rename; info will contain the new name
    my $physname = $row->{physname};
    my $itempaths = $self->_get_current_item_paths();

    my $physinfo = $gPhysInfo{$physname};

    if (!defined $physinfo) {
        $self->{errmsg} = "Attempt to rename unknown item '$physname':\n"
            . $self->{nameResolveSeen};

        return 0;
    }

    # A rename of an item renames it in all its shares
    $physinfo->{name} = $row->{info};

    $self->{itempaths} = $itempaths;
    $self->{info} = $self->_get_current_item_name();

    return 1;
}  #  End _rename_handler

###############################################################################
#  _share_handler
###############################################################################
sub _share_handler {
    my($self) = @_;
    my $row = $self->{row};

    my $physname = $row->{physname};
    my $physinfo = $gPhysInfo{$physname};

    if (!defined $physinfo) {
        $self->{errmsg} = "Attempt to share unknown item '$physname':\n"
            . $self->{physname_seen};

        return 0;
    }

    push @{ $physinfo->{sharedphys} }, $row->{parentphys};

    # 'itempaths' is the path for this new location (the share target);
    # 'info' contains the source path
    my $parentpaths = $self->_get_item_paths($row->{parentphys}, 1);

    $self->{itempaths} = [$parentpaths->[0] . $physinfo->{name}];
    $self->{info} = $self->_get_current_item_paths(1)->[0];

    return 1;

}  #  End _share_handler

###############################################################################
#  _branch_handler
###############################################################################
sub _branch_handler {
    my($self) = @_;
    my $row = $self->{row};

    # Branching a file is actually a null action in SVN; it simply means we
    # stop duplicating checkins. Return the existing path, but internally
    # we'll remove this parent from the list of shared physical parents from
    # the old location, then create a new one with the pertinent info. The row's
    # 'physname' is that of the new file; 'info' is the formerly shared file.

    my $physname = $row->{physname};
    my $oldphysname = $row->{info};

    my $oldphysinfo = $gPhysInfo{$oldphysname};

    # First delete this parentphys from the old shared object; see
    # _delete_handler for details
    if ($oldphysinfo->{parentphys} eq $row->{parentphys}) {
        $oldphysinfo->{parentphys} = shift( @{ $oldphysinfo->{sharedphys} } );
    } else {
        my $sharedphys = [];

        foreach my $oldparent (@{ $oldphysinfo->{sharedphys} }) {
            push @$sharedphys, $oldparent
                unless $oldparent eq $row->{parentphys};
        }

        $oldphysinfo->{sharedphys} = $sharedphys;
    }

    # Now create a new entry for this branched item
    $gPhysInfo{$physname} =
        {
         type       => $row->{itemtype},
         name       => $row->{itemname},
         parentphys => $row->{parentphys},
         sharedphys => [],
        };

    $self->{itempaths} = $self->_get_current_item_paths(1);

    return 1;

}  #  End _branch_handler

###############################################################################
#  _move_handler
###############################################################################
sub _move_handler {
    my($self) = @_;
    my $row = $self->{row};

    # Get the existing paths before the move; parent sub will get the new
    # name
    my $physname = $row->{physname};
    my $itempaths = $self->_get_current_item_paths();

    my $physinfo = $gPhysInfo{$physname};

    if (!defined $physinfo) {
        $self->{errmsg} = "Attempt to rename unknown item '$physname':\n"
            . $self->{physname_seen};

        return 0;
    }

    # Only projects can have true "moves", and projects don't have shares, so
    # we don't need to worry about any shared paths
    $physinfo->{parentphys} = $row->{parentphys};

    # 'itempaths' has the original path; 'info' has the new
    $self->{itempaths} = $itempaths;
    $self->{info} = $self->_get_current_item_paths(1)->[0];

    return 1;

}  #  End _move_handler

###############################################################################
#  _delete_handler
###############################################################################
sub _delete_handler {
    my($self) = @_;
    my $row = $self->{row};

    # For a delete operation we return only the "main" path, since any deletion
    # of shared paths will have their own entry

    my $physname = $row->{physname};

    my $itempaths = $self->_get_current_item_paths(1);

    my $physinfo = $gPhysInfo{$physname};

    if (!defined $physinfo) {
        $self->{errmsg} =  "Attempt to delete unknown item '$physname':\n"
            . $self->{physname_seen};
        return 0;
    }

    if ($physinfo->{parentphys} eq $row->{parentphys}) {
        # Deleting from the "main" parent; find a new one by shifting off the
        # first shared path, if any; if none exists this will leave a null
        # parent entry. We could probably just delete the whole node at this
        # point.

        $physinfo->{parentphys} = shift( @{ $physinfo->{sharedphys} } );

    } else {
        my $sharedphys = [];

        foreach my $parent (@{ $physinfo->{sharedphys} }) {
            push @$sharedphys, $parent
                unless $parent eq $row->{parentphys};
        }

        $physinfo->{sharedphys} = $sharedphys;
    }

    $self->{itempaths} = $itempaths;

    return 1;

}  #  End _delete_handler

###############################################################################
#  _recover_handler
###############################################################################
sub _recover_handler {
    my($self) = @_;
    my $row = $self->{row};

    my $physname = $row->{physname};

    my $physinfo = $gPhysInfo{$physname};

    if (!defined $physinfo) {
        $self->{errmsg} = "Attempt to recover unknown item '$physname':\n"
            . $self->{physname_seen};

        return 0;
    }

    if (defined $physinfo->{parentphys}) {
        # Item still has other shares, so recover it by pushing this parent
        # onto its shared list

        push( @{ $physinfo->{sharedphys} }, $row->{parentphys} );

    } else {
        # Recovering its only location; set the main parent back to this
        $physinfo->{parentphys} = $row->{parentphys};
    }

    # We only recover the path explicitly set in this row, so build the path
    # ourself by taking the path of this parent and appending the name
    my $parentpaths = $self->_get_item_paths($row->{parentphys}, 1);
    $self->{itempaths} = [$parentpaths->[0] . $physinfo->{name}];

    return 1;

}  #  End _recover_handler

###############################################################################
#  _get_current_item_paths
###############################################################################
sub _get_current_item_paths {
    my($self, $mainonly) = @_;

    return $self->_get_item_paths($self->{row}->{physname}, $mainonly);
}  #  End _get_current_item_paths

###############################################################################
#  _get_item_paths
###############################################################################
sub _get_item_paths {
    my($self, $physname, $mainonly) = @_;

    # Uses recursion to determine the current full paths for an item based on
    # the name of its physical file. We can't cache this information because
    # a rename in a parent folder would not immediately trigger a rename in
    # all of the child items.

    # By default, we return an anonymous array of all paths in which the item
    # is shared, unless $mainonly is true. Luckily, only files can be shared,
    # not projects, so once we start recursing we can set $mainonly to true.

    if (++($self->{recursed}) >= 1000) {
        $self->{errmsg} = "Infinite recursion detected while looking up "
            . "parent for '$physname':\n$self->{physname_seen}";

        return 0;
    }

    if ($physname eq 'AAAAAAAA') {
        # End of recursion; all items must go back to 'AAAAAAAA', which was so
        # named because that's what most VSS users yell after using it much. :-)
        return ['/'];
    }

    my $physinfo = $gPhysInfo{$physname};

    if (!defined $physinfo) {
        $self->{errmsg} = "Could not determine real path for '$physname':\n"
            . $self->{physname_seen};

        return undef;
    }

    $self->{physname_seen} .= "$physname, ";

    my @pathstoget = $mainonly? ($physinfo->{parentphys}) :
        ($physinfo->{parentphys}, @{ $physinfo->{sharedphys} } );

    my $paths = [];
    my $result;

    foreach my $parent (@pathstoget) {
        if (!defined $parent) {
            1;
        }
        $result = $self->_get_item_paths($parent, 1, 1);

        if(!defined $result) {
            return undef;
        }

        push @$paths, $result->[0] . $physinfo->{name};
    }

    return $paths;

}  #  End _get_item_paths

###############################################################################
#  _get_current_item_name
###############################################################################
sub _get_current_item_name {
    my($self) = @_;

    my $physname = $self->{row}->{physname};
    my $physinfo = $gPhysInfo{$physname};

    if (!defined $physinfo) {
        $self->{errmsg} = "Could not determine real name for '$physname':\n"
            . $self->{physname_seen};
        return undef;
    }

    return $physinfo->{name};
}  #  End _get_current_item_name



1;