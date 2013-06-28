r"""
AUTHORS: 

- Thierry Coulbois (2013-05-16): beta.0 version 
"""
#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
# 
#  Distributed under the terms of the GNU General Public License (GPL) 
#                  http://www.gnu.org/licenses/ 
#***************************************************************************** 
	 
def test(rang,longueur,nombre):
    F=FreeGroup(rang)

    stat=0
    t=cputime()

    for i in xrange(nombre):
        phi=F.random_automorphism(longueur)
        print i,":",phi
        f=phi.train_track(stable=True,relative=True)
        if len(f._strata)==1: 
            stat=stat+1
        print f
        print "-------------------------"
        
    print "rang: ",rang,"longueur: ",longueur," time: ",cputime(t)/nombre," train-tracks: %.1f"%(stat/nombre*100)

def test_stat(rangs,longueurs,puissance):
    for n in rangs:
        F=FreeGroup(n)
        for l in longueurs:
            stat=0
            t=cputime()
            for i in xrange(puissance):
                phi=F.random_automorphism(l)
                try:
                    f=phi.train_track(relative=True,stable=True)
                    if len(f._strata)==1: 
                        stat+=1
                except Exception as err:
                    print phi
                    print err
            print "rang: ",n,"longueur: ",l," time: ",cputime(t)/puissance," train-tracks: %.1f"%(stat/puissance*100)


def bugs():
    """
    Returns a list of free group automorphisms, that created bugs at
    some previous stage of developpment of this program while
    computing stable relative train-tracks.
    
    This is a good list to test futur corrections.
    """
    
    result=[]

    # Problems while computing INPs of the RTT
    phi=FreeGroupAutomorphism("a->BafD,b->bcdFAbfbFBafDCB,c->dFAbbcdFAbfb,d->dFAbfeFdBBFBafDCB,e->eF,f->bcdFAbfbdFAbfb",FreeGroup(6))
    result.append(phi)    

    phi=FreeGroupAutomorphism("a->efea,b->Ebcc,c->c,d->CBedaBFECBedaBe,e->CCBeAEF,f->efbADEbcEbcc",FreeGroup(6))
    result.append(phi)

    #The folding of an INP requires folding a path as a full edge
    phi=FreeGroupAutomorphism("a->BaBaBBFbAcEC,b->bAbce,c->Ac,d->dBfbbAbAbceCa,e->ceCa,f->BfbCaECBaB",FreeGroup(6))
    result.append(phi)

    #There is an essential INP in a stratum
    phi=FreeGroupAutomorphism("a->FbccbcaB,b->bc,c->bcbcc,d->bAdCB,e->bAbAdbcebA,f->f",FreeGroup(6))
    result.append(phi)

    #An inessential connecting path not so easy to fold
    phi=FreeGroupAutomorphism("a->aDacAd,b->BCbcb,c->bcb,d->BAdA",FreeGroup(4))
    result.append(phi)

    #An inessential connecting path not so easy to fold
    phi=FreeGroupAutomorphism("a->baB,b->b,c->bAAAdcbbAbAAAdcbDa,d->AdBCDaaaB",FreeGroup(4))
    result.append(phi)
    
    #An essential INP in stratum 0, and two exponential strata
    phi=FreeGroupAutomorphism("a->BCBCaBCBCdabcba,b->bcb,c->cb,d->BCBCaBCBCdabcb",FreeGroup(4))
    result.append(phi)
    
    #Difficult inessential connecting path
    phi=FreeGroupAutomorphism("a->a,b->baEaba,c->Acdc,d->CDCBAecd,e->ABAeCDCAcdc",FreeGroup(5))
    result.append(phi)

    #Difficult INP
    phi=FreeGroupAutomorphism("a->CaBe,b->CedcEbCede,c->cEbCed,d->CedcEbCed,e->DEcBeDEcBeC",FreeGroup(5))
    result.append(phi)

    #Problem to correctly detect lines to fusion
    phi=FreeGroupAutomorphism("a->daBacdbADC,b->dacdbADc,c->c,d->daB",FreeGroup(4))
    result.append(phi)

    #A complicated line to fusion
    phi=FreeGroupAutomorphism("a->gBDaidbFe,b->Chdb,c->h,d->EfBDIGdd,e->HHcidbFee,f->Ef,g->DgidbFe,h->Chh,i->EfBDIAdbGidb",FreeGroup(9))
    result.append(phi)

    #Yet another inessential connecting path difficult to fold
    phi=FreeGroupAutomorphism("a->DABBadBdBadBcDABadadBadBcDAbad,b->DAbad,c->DABadBdBadBcDAbad,d->Bd",FreeGroup(4))
    result.append(phi)

    return result


def bug_test():
    bugs_list=bugs()
    for i,phi in enumerate(bugs_list):
        print "\n\n------------------------------------"
        print i,":",phi
        f=phi.train_track(stable=True,relative=True,verbose=True)
            
