#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
# 
#  Distributed under the terms of the GNU General Public License (GPL) 
#                  http://www.gnu.org/licenses/ 
#***************************************************************************** 
from sage.combinat.words.morphism import WordMorphism

class FreeGroupAutomorphism(WordMorphism):
    """
    Free group automorphism. 

    EXAMPLES::

    sage: F=FreeGroup(3)
    sage: FreeGroupAutomorphism("a->ab,b->ac,c->a",F)
    Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

    sage:FreeGroupAutomorphism("a->ab,b->ac,c->a")
    Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

    sage: map={}
    sage: map['a']='ab'
    sage: map['b']='ac'
    sage: map['c']='a'
    sage: FreeGroupAutomorphism(map)
    Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

    AUTHORS: 
 
    - Thierry Coulbois (2013-05-16): beta.0 version 
	 
    """
    
    def __init__(self,data,group=None):
        """
        Builds a FreeGroupAutomorphism from data.
        """
        if group is not None and not isinstance(group, FreeGroup):
            raise ValueError, "the group must be a Free Group"

        WordMorphism.__init__(self,data)

        if group is None:
            A = AlphabetWithInverses(self.domain().alphabet())
            F = FreeGroup(A)
        else:
            F = group
            A = group.alphabet()

        self._domain = F
        self._codomain = F  # unuseful... consistency with WordMorphism
        for letter in self._morph.keys():
            self._morph[letter]=F.reduce(self._morph[letter])
            self._morph[A.inverse_letter(letter)] = F.inverse_word(self._morph[letter])
        
    def __call__(self,w,order=1):
        """
        Apply the automorphism to the word w.

        WARNING:

        if w is a letter of the alphabet which is iterable it will be considered as a word.
        """    
        F=self.codomain()
        while order>0:
            result=F()
            order=order-1
            for a in w:
                result=result*self.image(a)
            w=result    
        return result
        
    def __mul__(self, other):
        """
        Returns the composition self*other.
        """
        if isinstance(other,FreeGroupAutomorphism):
            m = dict((a,self(other.image(a))) for a in other.domain().alphabet().positive_letters())
            return FreeGroupAutomorphism(m,self.domain())
        else:
            return WordMorphism.__mul__(self,other)

    def __pow__(self,other):
        """
        returns self^other, where other is an integer.
        """
        if other>0:
            if other%2==0:
                phi=pow(self,other/2)
                return phi*phi
            elif other>2:
                phi=pow(self,(other-1)/2)
                return phi*phi*self
            else: #other==1
                return self
        elif other<0:
            return pow(self.inverse(),-other)
        else: #other==0
            return self._domain.identity_automorphism()

    def __str__(self):
        """
        String representation.
        """
        result=""
        for letter in self.domain().alphabet().positive_letters():
            result += letter + "->"
            for a in self.image(letter):
                result+=a
            result+=","
        return result[:-1]        
                 
    def __repr__(self):
        result="Automorphism of the %s: " %str(self._domain)
        result=result+"%s" %str(self)
        return result

    def size(self):
        """
        Size of the automorphism: half the maximum length of the image of a two letter word.
        """
        result=0
        A=self._domain._alphabet
        for a in A:
            for b in A:
                if a!=A.inverse_letter(b):                    
                    l=len(self(self.domain([a,b])))
                    if result<l:
                        result=l
        return result/2
 
    def is_permutation(self):
        """
        True if self is a permutation of the alphabet.
        """
        return not any(len(self.image(a))!=1 for a in self._domain._alphabet.positive_letters()) 
      
       
    def _inverse_permutation(self):
        """
        inverse self if it is a permutation
        """
        F= self.domain()
        A=F.alphabet()
        result = {}
        for a in A.positive_letters():
            b = self.image(a)[0]
            if A.is_positive_letter(b):
                result[b] = F([a])
            else:
                result[A.inverse_letter(b)] = F([A.inverse_letter(a)])

        return FreeGroupAutomorphism(result,group=self._domain)
                

    def _inverse_rec(self,other,verbose):
        """
        Use Dehn twists to successively put self as identity and other as the
        inverse of self.

        NOT TO BE USED DIRECTLY
        """
        if verbose: print self, other

        F = self._domain
        A = F.alphabet()
    
        # trivial case
        if self.is_permutation():
            return other*self._inverse_permutation()

        # the other one
        else:
            delta = -1

            for x in A:
                w1=self.image(x)
                
                for y in A:
                    if (x!=y and x!=A.inverse_letter(y)):
                        w2=self.image(y)
                        w3=w1*w2
                        d=F.nielsen_strictly_less(w3,w1)
                        if (delta<d and d>=0):
                            delta=d
                            a=x
                            b=y
                            
                        
                        
            if (delta==-1):
                raise ValueError("%s is non invertible" %str(self))
            else:
                other = other*F.dehn_twist(a,b)
                return (self*F.dehn_twist(a,b))._inverse_rec(other,verbose)
    
     
    def inverse(self,verbose=False):
        """
        Inverse the automorphism.

        EXAMPLES::

        sage: F=FreeGroup(3)
        sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a",F)
        sage: phi.inverse()
        Automorphism of the Free group over ['a', 'b', 'c']: a->c,b->Ca,c->Cb

        """
        return self._inverse_rec(self._domain.identity_automorphism(),verbose)

    def simple_outer_representative(self):
        """
        Returns the shortest representative of the outer class of self.

        EXAMPLES::

        sage: F=FreeGroup(3)
        sage: phi=FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac",F)
        sage phi.simple_outer_representative()
        Automorphism of the Free group over ['a', 'b', 'c']: a->c,b->Ca,c->Cb

        """
        F=self._domain
        A=F._alphabet
        l=len(A)
        result=dict(((a,self.image(a)) for a in A.positive_letters()))
        done=False
        while not done:
            done=True
            gain=dict(((a,0) for a in A))
            for a in A.positive_letters():                    
                gain[result[a][0]]+=1
                gain[A.inverse_letter(result[a][-1])]+=1
            for a in A:
                if gain[a]>l:
                    done=False
                    b=a
            if not done:
                B=A.inverse_letter(b)
                for a in A.positive_letters():
                    if result[a][0]==b and result[a][-1]==B:
                        result[a]=result[a][1:-1]
                    elif result[a][0]==b:
                        result[a]=result[a][1:]+Word(b)
                    elif result[a][-1]==B:
                        result[a]=Word(B)+result[a][:-1]
                    else:
                        result[a]=Word(B)+result[a]+Word(b)
                                        
        return FreeGroupAutomorphism(result,F)
    
    def rose_representative(self):
        """
        Topological representative on the rose on the alphabet.
        """

        return TopologicalRepresentative(MarkedGraph.rose_marked_graph(self._domain.alphabet()),self)

    def train_track(self,stable=True,relative=True,verbose=False):
        """
        Computes a train-track representative of self. 

        According to the options computes a relative (or ends when
        finding a reduction) and/or stable (with at most one INP
        crossing each exponential stratum). verbose can be either True
        or a positive number giving details on the computations.
        
        OUTPUT: 

        A topological representative of self. 

        - If relative=False, this topological representative is either
        an absolute train-track or fixes a subgraph (with a non
        contractible connected component).
        
        - If relative=True, the output is a relative train-track

        - If stable=True, the output is either a stable absolute
          train-track or stable relative train-track or (if
          relative=False) fixes a subgraph (with a non contractible
          connected component).

        """
        f=self.rose_representative()
        f.train_track(verbose)
        if stable and len(f._strata)==1:
            f._stabilize(verbose)
        if relative and len(f._strata)>1:
            if stable:
                f.stable_relative_train_track(verbose)
            else:
                f.relative_train_track(verbose)
        return f
        
    @staticmethod
    def tribonacci():
        """
        Tribonacci automorphism.
        """
        return FreeGroupAutomorphism("a->ab,b->ac,c->a",FreeGroup(3))

    @staticmethod
    def Handel_Mosher_inverse_with_same_lambda():
        """
        Example given in the introduction of Handel, Mosher,
        parageometric outer automorphisms of free groups, Transactions
        of Amer. Math. Soc. 359, 3153-3183, 2007. phi is iwip has the
        same expansion factor as its inverse: 3.199. phi is not
        geometric and not parageometric.
        """
        F=FreeGroup(3)
        theta=pow(FreeGroupAutomorphism("a->b,b->c,c->Ba",F),4)
        psi=FreeGroupAutomorphism("a->b,b->a,c->c",F)
        return psi*theta*psi*theta.inverse()


    @staticmethod
    def Bestvina_Handel_example_1_1():
        """ 
        Automorphism given as Example 1.1 in Bestvina, Handel, Train
        tracks and automorphisms of free groups, Annals of Math, 135,
        1-51, 1992.
        """
        return FreeGroupAutomorphism("a->b,b->c,c->d,d->ADBC",FreeGroup(4))
   


    @staticmethod
    def Bestvina_Handel_example_1_9():
        """ 
        Automorphism given as Example 1.9 in Bestvina, Handel, Train
        tracks and automorphisms of free groups, Annals of Math, 135,
        1-51, 1992.

        This automorphism cannot be represented by an absolute
        train-track. But the representation on the rose is a relative
        train-track.
        """
        return FreeGroupAutomorphism("a->ba,b->bba,c->cAbaB",FreeGroup(3))
    
    @staticmethod
    def Bestvina_Handel_example_3_6():
        """ 
        Automorphism given as Example 3.6 in Bestvina, Handel, Train
        tracks and automorphisms of free groups, Annals of Math, 135,
        1-51, 1992.

        This automorphism is train-track on the rose and has an
        indivisble Nielsen path in A.b which is inessential.
        """
        return FreeGroupAutomorphism("a->ba,b->bba",FreeGroup(2))

    @staticmethod
    def Bestvina_Handel_example_5_16():
        """ 
        Automorphism given as Example 5.16 in Bestvina, Handel, Train
        tracks and automorphisms of free groups, Annals of Math, 135,
        1-51, 1992.

        This automorphism occurs as a pseudo-Anosov homeomorphism of
        the four-times punctured phere.  
        """
        return FreeGroupAutomorphism("a->a,b->CAbac,c->CAbacacACABac",FreeGroup(3))

    @staticmethod
    def Handel_Mosher_axes_3_4():
        """ 
        Automorphism given in Section 3.4 of Handel, Mosher, axes
        in Outer space, Mem. Amer. Math. Soc. 213, 2011.
        
        This automorphism is iwip, not geometric and is train-track on
        the rose. It has expansion factor 4.0795. Its inverse is not
        train-track on the rose and has expansion factor 2.46557. It
        also appears in Section 5.5 of the paper.
        """
        A=AlphabetWithInverses(['a','g','f'],['A','G','F'])
        return FreeGroupAutomorphism("a->afgfgf,f->fgf,g->gfafg",FreeGroup(A))

    @staticmethod
    def Handel_Mosher_axes_5_5():
        """ 
        Automorphism given in Section 5.5 of Handel, Mosher, axes
        in Outer space, Mem. Amer. Math. Soc. 213, 2011.
       
        This automorphism phi is iwip and not geometric. Both phi and
        phi.inverse() are train-track on the rose. phi has expansion
        factor 6.0329 while phi.inverse() has expansion factor
        4.49086.
        """
        return FreeGroupAutomorphism("a->bacaaca,b->baca,c->caaca",FreeGroup(3))

    @staticmethod
    def Hilion_parabolic(k=1):
        """ 
        Automorphism given in Section 2 of Hilion.
       
        This automorphism has a parabolic orbit inside F_4.
        """
        F=FreeGroup(4)
        phi=FreeGroupAutomorphism("a->a,b->ba,c->caa,d->dc",F)
        if k>1:
            phi=phi*pow(F.dehn_twist(c,a),k-1)
        return phi

    @staticmethod
    def Handel_Mosher_parageometric_1():
        """ 
        Automorphism given in the introduction of Handel, Mosher,
        parageometric outer automorphisms of free groups, Transactions
        of Amer. Math. Soc. 359, 3153-3183, 2007.
       
        This automorphism phi is iwip, not geometric and
        parageometric. Both phi and phi.inverse() are train-track on
        the rose. phi has expansion factor 1.46557 while phi.inverse()
        has expansion factor 1.3247.
        """
        return FreeGroupAutomorphism("a->ac,b->a,c->b",FreeGroup(3))

    @staticmethod
    def Cohen_Lustig_1_6():
        """ 

        Automorphism given as example 1.6 in Cohen, Lustig, on the
        dynamics and the fixed subgroup of a free group automorphism,
        Inventiones Math. 96, 613-638, 1989.

        """
        return FreeGroupAutomorphism("a->cccaCCC,b->CaccAbC,c->accAbccaCCBaCCAccccACCC",FreeGroup(3))

    @staticmethod
    def Cohen_Lustig_7_2():
        """ 

        Automorphism given as example 7.2 in Cohen, Lustig, on the
        dynamics and the fixed subgroup of a free group automorphism,
        Inventiones Math. 96, 613-638, 1989.

        """
        return FreeGroupAutomorphism("a->aabc,b->abc,c->abcc",FreeGroup(3))

    @staticmethod
    def Cohen_Lustig_7_3():
        """ 

        Automorphism given as example 7.3 in Cohen, Lustig, on the
        dynamics and the fixed subgroup of a free group automorphism,
        Inventiones Math. 96, 613-638, 1989.

        """
        return FreeGroupAutomorphism("a->cabaa,b->baa,c->caba",FreeGroup(3))

    @staticmethod
    def Turner_Stallings():
        """ 
        Automorphism of F_4 given in [Turner].

        This automorphism comes from an idea of Stallings and although
        it is very short, it has a very long fixed word.

        """
        return FreeGroupAutomorphism("a->dac,b->CADac,c->CABac,d->CAbc",FreeGroup(4))
