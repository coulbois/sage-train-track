sage-train-track
================

Free group automorphisms and train-track representatives in python/sage. 

This is a Sage optional package. It contains code to handle free group
automorphisms (inversion, composition, etc.) and to compute
train-track representatives (absolute and relative, stable and
unstable) as defined by Bestvina and Handel. This includes the
computation of Nielsen paths and indices of iwip automorphisms and
much more. Convex cores of pairs of tree as defined by Guirardel also
appear.

Installation::

  sage -pip install train_track

Warning: it seems that Mac OS X 10.13 and later has a security
conflict between SIP and SSL and does not succeed in downloading the
package from https://pypi.python.org. To overcome this difficulty,
just download the tarball train_track-0.1.4.tar.gz from

  https://pypi.python.org/simple/train_track

and run::

  sage -pip install /path/to/train_track-0.1.4.tar.gz

Warning: if you lack intstallation privilege, you can install only for
yourself::

  sage -pip install --user train_track
  
On Cocalc.com installation can be done either from a terminal as above
or from a cell::

  !sage -pip install train_track

Warning, Cocalc free accounts do not have access to internet, first
download the tarball then install.
  
Usage::

    sage: from train_track import *


After this command, you can play with free groups and their automorphisms::

    sage: FreeGroup('a,b,c')
    Free Group on generators {a, b, c}
    sage: FreeGroupAutomorphism('a->bCb,b->Bc,c->BcBa')
    Automorphism of the Free Group on generators {a, b, c}: a->a*b,b->a*c,c->a
    sage: free_group_automorphisms.Cohen_Lustig_1_6()
    Automorphism of the Free Group on generators {a, b, c}: a->c^3*a*c^-3,b->c^-1*a*c^2*a^-1*b*c^-1,c->a*c^2*a^-1*b*c^2*a*c^-2*b^-1*a*c^-2*a^-1*c^4*a^-1*c^-3
    
