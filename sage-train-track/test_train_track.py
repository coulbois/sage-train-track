# coding=utf-8
r""" test_train_track.py testing module for train_track
to run with long option

./sage -t --long src/sage/combinat/words/test_train_track.py

AUTHORS:

- Thierry COULBOIS (2013-01-01): initial version
- Dominique BENIELLI (2016-02_15):
  AMU University <dominique.benielli@univ-amu.fr>, Integration in SageMath


"""
#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
# 
#  Distributed under the terms of the GNU General Public License (GPL) 
#                  http://www.gnu.org/licenses/ 
#***************************************************************************** 
from sage.combinat.words.free_group import FreeGroup
from sage.combinat.words.free_group_automorphism import FreeGroupAutomorphism
from sage.misc.misc import cputime


def test(rang, longueur, nombre):
    """
    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version

    TESTS:

        sage: from sage.combinat.words.test import *
        sage: test(3, 1, 1) # long time (80s on sage.math, 2016) # random
        0 : a->a,b->b,c->ac
        Graph self map:
        Marked graph: a: 0->0, b: 0->0, c: 0->0
        Marking: a->a, b->b, c->c
        Edge map: a->a, b->b, c->ac
        Strata: [set(['a']), set(['c']), set(['b'])]
        -------------------------
        rang:  3 longueur:  1  time:  0.024  train-tracks: 0.0

    """

    F = FreeGroup(rang)

    stat = 0
    t = cputime()

    for i in xrange(nombre):
        phi = FreeGroupAutomorphism.random_automorphism(F, longueur)
        print i, ":", phi
        f = phi.train_track(stable=True, relative=True)
        if len(f._strata) == 1:
            stat = stat + 1
        print f
        print "-------------------------"
        
    print "rang: ", rang, "longueur: ", longueur, " time: ", \
        cputime(t) / nombre, " train-tracks: %.1f" % (stat/nombre*100)


def test_stat(rangs, longueurs, puissance):
    """
    TESTS:

        sage: from sage.combinat.words.test import *
        sage: test_stat([2,3], [3,2], 1) # long time (80s ) # random
        rang:  2 longueur:  3  time:  0.084  train-tracks: 100.0
        rang:  2 longueur:  2  time:  0.076  train-tracks: 100.0
        rang:  3 longueur:  3  time:  0.012  train-tracks: 0.0
        rang:  3 longueur:  2  time:  0.00800000000004  train-tracks: 0.0


    AUTHORS:

    - Thierry Coulbois(2013 - 05 - 16): beta .0 version

    """
    for n in rangs:
        F = FreeGroup(n)
        for l in longueurs:
            stat = 0
            t = cputime()
            for i in xrange(puissance):
                phi = FreeGroupAutomorphism.random_automorphism(F, l)
                try:
                    f = phi.train_track(relative=True, stable=True)
                    if len(f._strata) == 1:
                        stat += 1
                except Exception as err:
                    print phi
                    print err
            print "rang: ", n, "longueur: ", l, " time: ", \
                cputime(t) / puissance, \
                " train-tracks: %.1f" % (stat / puissance * 100)


def bugs():
    """
    Returns a list of free group automorphisms, that created bugs at
    some previous stage of developpment of this program while
    computing stable relative train-tracks.
    
    This is a good list to test futur corrections.

    AUTHORS:

    - Thierry Coulbois(2013 - 05 - 16): beta .0 version

    TESTS:

        sage: from sage.combinat.words.test import *
        sage: bugs() # long time (80s ) # random
        0 : a->BafD,b->bcdFAbfbFBafDCB,c->dFAbbcdFAbfb,d->dFAbfeFdBBFBafDCB,e->eF,f->bcdFAbfbdFAbfb

    """
    
    result = []

    # Problems while computing INPs of the RTT
    phi = FreeGroupAutomorphism("a->BafD,b->bcdFAbfbFBafDCB,c->dFAbbcdFAbfb,"
                                "d->dFAbfeFdBBFBafDCB,e->eF,f->bcdFAbfbdFAbfb",
                                FreeGroup(6))
    result.append(phi)    

    phi = FreeGroupAutomorphism("a->efea,b->Ebcc,c->c,d->CBedaBFECBedaBe,"
                                "e->CCBeAEF,f->efbADEbcEbcc", FreeGroup(6))
    result.append(phi)

    # The folding of an INP requires folding a path as a full edge
    phi = FreeGroupAutomorphism("a->BaBaBBFbAcEC,b->bAbce,"
                                "c->Ac,d->dBfbbAbAbceCa,e->ceCa,"
                                "f->BfbCaECBaB", FreeGroup(6))
    result.append(phi)

    # There is an essential INP in a stratum
    phi = FreeGroupAutomorphism("a->FbccbcaB,b->bc,c->bcbcc,d->bAdCB,"
                                "e->bAbAdbcebA,f->f", FreeGroup(6))
    result.append(phi)

    # An inessential connecting path not so easy to fold
    phi = FreeGroupAutomorphism("a->aDacAd,b->BCbcb,c->bcb,d->BAdA",
                                FreeGroup(4))
    result.append(phi)

    # An inessential connecting path not so easy to fold
    phi = FreeGroupAutomorphism("a->baB,b->b,c->bAAAdcbbAbAAAdcbDa,"
                                "d->AdBCDaaaB", FreeGroup(4))
    result.append(phi)
    
    # An essential INP in stratum 0, and two exponential strata
    phi = FreeGroupAutomorphism("a->BCBCaBCBCdabcba,b->bcb,c->cb,"
                                "d->BCBCaBCBCdabcb", FreeGroup(4))
    result.append(phi)
    
    # Difficult inessential connecting path
    phi = FreeGroupAutomorphism("a->a,b->baEaba,c->Acdc,d->CDCBAecd,"
                              "e->ABAeCDCAcdc", FreeGroup(5))
    result.append(phi)

    # Difficult INP
    phi = FreeGroupAutomorphism("a->CaBe,b->CedcEbCede,c->cEbCed,"
                               "d->CedcEbCed,e->DEcBeDEcBeC", FreeGroup(5))
    result.append(phi)

    # Problem to correctly detect lines to fusion
    phi = FreeGroupAutomorphism("a->daBacdbADC,b->dacdbADc,c->c,d->daB",
                                FreeGroup(4))
    result.append(phi)

    # A complicated line to fusion
    phi = FreeGroupAutomorphism("a->gBDaidbFe,b->Chdb,c->h,d->EfBDIGdd,"
                                "e->HHcidbFee,f->Ef,g->DgidbFe,h->Chh,"
                                "i->EfBDIAdbGidb", FreeGroup(9))
    result.append(phi)

    # Yet another inessential connecting path difficult to fold
    phi = FreeGroupAutomorphism("a->DABBadBdBadBcDABadadBadBcDAbad,"
                              "b->DAbad,c->DABadBdBadBcDAbad,d->Bd",
                              FreeGroup(4))
    result.append(phi)

    # Braids of Mark Bell which causes difficulties
    F = FreeGroup(4)

    phi = FreeGroupAutomorphism.identity_automorphism(F)
    # Difficulties in folding an inessential INP in the relative
    # train-track: need to fold inessential connecting paths in the
    # process
    for i in [1, -2, 3, 1, 1, 3, 2, -1, 2, 2, -3]:
        phi *= FreeGroupAutomorphism.braid_automorphism(F, abs(i), i < 0)
    result.append(phi)

    phi = FreeGroupAutomorphism.identity_automorphism(F)
    # Difficulties in folding an inessential INP in the relative
    # train-track: need to fold inessential connecting paths in the
    # process
    for i in [-2, 3, -2, -1, -1]:
        phi *= FreeGroupAutomorphism.braid_automorphism(F, abs(i), i < 0)
    result.append(phi)

    phi = FreeGroupAutomorphism.identity_automorphism(F)
    # Difficulties in folding an inessential INP in the relative
    # train-track: need to fold inessential connecting paths in the
    # process
    for i in [2, -1, 2, 3, 3]:
        phi *= FreeGroupAutomorphism.braid_automorphism(F, abs(i), i < 0)
    result.append(phi)

    phi = FreeGroupAutomorphism.identity_automorphism(F)
    # Difficulties in folding an inessential connecting paths: chosing cleverly the order.
    for i in [-2, -1, -1, -2, 3]:
        phi *= FreeGroupAutomorphism.braid_automorphism(F, abs(i), i < 0)
    result.append(phi)

    return result


def bug_test():
    """
    AUTHORS:

    - Thierry
    Coulbois(2013 - 05 - 16): beta.0 version

    TESTS:

    sage: from sage.combinat.words.test import *
    sage: bug_test()  # long time (50 second) # random

    """
    bugs_list = bugs()
    for i, phi in enumerate(bugs_list):
        print "\n\n------------------------------------"
        print i, ":", phi
        f = phi.train_track(stable=True, relative=True, verbose=True)
