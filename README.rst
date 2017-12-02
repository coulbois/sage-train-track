sage-train-track
================

Free group automorphisms and train-track representative in python/sage. 

This is a Sage optional package. It contains code to handle free group
automorphisms (inversion, composition, etc.) and to compute
train-track representatives (absolute and relative, stable and
unstable) as defined by Bestvina and Handel. This includes the
computation of Nielsen paths and indices of iwip automorphisms and
much more. Convex cores of pairs of tree as defined by Guirardel also
appear.

Installation::

  sage -pip install train_track

(warning it seems that Mac OS X 10.13 has a security conflict between
SIP and SSL and does not succeed in downloading the package from
https://pypi.python.org. To overcome this difficulty, just download
the tarball train_track-0.1.0.tar.gz from

  https://pypi.python.org/simple/train_track

and run::

  sage -pip install path/to/train_track-0.1.0.tar.gz

)
  
Usage::

    sage: from train_track import *


After this command, you can play with free groups and their automorphisms::

    sage: FreeGroup('abc')
    Free group over ['a', 'b', 'c']
    sage: FreeGroupAutomorphism('a->bCb,b->Bc,c->BcBa')
    Automorphism of the Free group over ['a', 'b', 'c']: a->bCb,b->Bc,c->BcBa
    sage: free_group_automorphisms.Cohen_Lustig_1_6()
    Automorphism of the Free group over ['a', 'b', 'c']: a->cccaCCC,b->CaccAbC,c->accAbccaCCBaCCAccccACCC
