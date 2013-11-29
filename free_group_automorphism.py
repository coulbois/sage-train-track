#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from inverse_alphabet import AlphabetWithInverses
from sage.combinat.words.morphism import WordMorphism
from free_group import FreeGroup

class FreeGroupMorphism(WordMorphism):
    def __init__(self,data,group=None):
        """
        Builds a FreeGroupAutomorphism from data.

        INPUT:

        - ``data`` - the data used to build the morphism

        - ``group`` - an optional free group
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

        .. WARNING::

        if w is a letter of the alphabet which is iterable it will be considered
        as a word. If you want the image of a letter use :meth:`image` instead.
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
        if isinstance(other,FreeGroupMorphism):
            m = dict((a,self(other.image(a))) for a in other.domain().alphabet().positive_letters())
            return FreeGroupMorphism(m,self.domain())
        return super(FreeGroupMorphism, self).__mul__(other)

    def __pow__(self, n):
        """
        returns self^n, where other is an integer.

        TESTS::

            sage: f = FreeGroupAutomorphism('a->ab,b->A')
            sage: f**-3
            Automorphism of the Free group over ['a', 'b']: a->bAB,b->baBAB
        """
        if n > 0:
            from sage.structure.element import generic_power
            return generic_power(self,n)
        elif n < 0:
            from sage.structure.element import generic_power
            return generic_power(self.inverse(), -n)
        else:
            return self.domain().identity_automorphism()

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
        result="Morphism of the %s: " %str(self._domain)
        result=result+"%s" %str(self)
        return result

    def to_automorphism(self):
        if not self.is_invertible():
            raise ValueError("the morphism is not invertible")
        return FreeGroupAutomorphism(dict((a,self.image(a)) for a in self.domain().alphabet().positive_letters()),
            domain=self.domain())

    def to_word_morphism(self):
        r"""
        Return a word morphism.

        .. NOTE::

            This method should not be there but on the other hand,
            f.periodic_points() fails for FreeGroupMorphism and
            FreeGroupAutomorphism

        EXAMPLES::

            sage: f = FreeGroupAutomorphism('a->AD,b->Adac,c->bd,d->c')
            sage: f.to_word_morphism().periodic_points()
            [[word: AdacccADDBdacADbdbdbddaCCCADacADbddaCAda...,
              word: dacADbdbdbddaCCCADacADbddaCAdaccAdaccAda...,
              word: cADbddaCAdaccAdaccAdacccADDBDBDBdaCADbdd...,
              word: bddaCAdacccADDBdacADbdbddacADbdbddacADbd...],
             [word: CCADaCCADacADDBdaCCCADaCCADacADDBdaCAdac...,
              word: DBDBdaCADDBDBdaCADbddaCCCADacADDBDBDBdaC...]]
        """
        return WordMorphism(dict((a,list(self.image(a))) for a in self.domain().alphabet()))

    def size(self):
        """
        Size of the endomorphism: half the maximum length of the image of a two letter word.

        .. TODO::

            the definition is ambiguous, do we take floor or ceil ?

        EXAMPLES::

            sage: FreeGroupMorphism('a->abc,b->,c->ccc').size()
            3
        """
        result=0
        D = self.domain()
        A=self._domain._alphabet
        for a in A:
            for b in A:
                if not A.are_inverse(a,b):
                    l = (self.image(a) * self.image(b)).length()
                    if result < l:
                        result = l
        return result // 2

    def is_permutation(self):
        """
        True if self is a permutation of the alphabet.

        EXAMPLES::

            sage: FreeGroupMorphism('a->a,b->b').is_permutation()
            True
            sage: FreeGroupMorphism('a->a,b->c,c->b').is_permutation()
            True
            sage: FreeGroupMorphism('a->a,b->b,c->b').is_permutation()
            False
            sage: FreeGroupMorphism('a->a,b->ba').is_permutation()
            False
        """
        A = self._domain._alphabet
        seen = set()
        for a in A.positive_letters():
            if len(self.image(a)) != 1 or a in seen:
                return False
            seen.add(a)
            seen.add(A.inverse_letter(a))
        return True

    def _inverse_permutation(self):
        """
        Return the inverse of ``self`` if it is a permutation
        """
        F = self.domain()
        A = F.alphabet()
        result = {}
        for a in A.positive_letters():
            b = self.image(a)[0]
            if A.is_positive_letter(b):
                result[b] = F([a])
            else:
                result[A.inverse_letter(b)] = F([A.inverse_letter(a)])

        return FreeGroupAutomorphism(result,group=self._domain)

    def is_invertible(self):
        """
        Use Dehn twists to successively to check wether ``self`` is invertible.

        EXAMPLES::

            sage: FreeGroupMorphism('a->b,b->a').is_invertible()
            True
            sage: FreeGroupMorphism('a->ab,b->a').is_invertible()
            True

            sage: FreeGroupMorphism('a->a,b->a').is_invertible()
            False
            sage: FreeGroupMorphism('a->ab,b->ba').is_invertible()
            False
            sage: FreeGroupMorphism('a->aa,b->b').is_invertible()
            False
        """
        f = self
        F = self._domain
        A = F.alphabet()

        while True:
            # trivial case
            if f.is_permutation():
                return True

            # the other one
            else:
                delta = -1

                for x in A:
                    w1 = f.image(x)
                    for y in A:
                        if (x != y and x != A.inverse_letter(y)):
                            w2 = f.image(y)
                            w3 = w1*w2
                            d = F.nielsen_strictly_less(w3,w1)
                            if (delta<d and d>=0):
                                delta = d
                                a = x
                                b = y

                if (delta==-1):
                    return False

                f = f * F.dehn_twist(a,b)

    def inverse(self):
        """
        Use Dehn twists to successively put ``self`` as identity and ``other`` as the
        inverse of ``self``.

        EXAMPLES::

            sage: phi = FreeGroupAutomorphism("a->ab,b->ac,c->a")
            sage: phi.inverse()
            Automorphism of the Free group over ['a', 'b', 'c']: a->c,b->Ca,c->Cb

        .. ALGORITHM::

            Implements the Nielsen-Whitehead algorithm: search for a Dehn
            twist that reduces the size of the automorphism.
        """
        F = self._domain
        A = F.alphabet()

        other = F.identity_automorphism()

        while True:
            # trivial case
            if self.is_permutation():
                return other * self._inverse_permutation()

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
                    self = self*F.dehn_twist(a,b)

    def length2_words(self):
        r"""
        Return the words of length 2 in the attracting language of ``self``.

        If the morphism is everywhere growing (a weaker condition than iwip)
        then there is a well defined notion of attracting lamination. If it is
        not the case, the output of this method should not be used.

        EXAMPLES::

            sage: f = FreeGroupMorphism('a->ab,b->a')
            sage: f.length2_words()
            [word: aa, word: ab, word: ba, word: AA, word: AB, word: BA]
        """
        D = self.domain()
        A = D.alphabet()
        assert D.domain() is self.codomain()
        wait = [D([a]) for a in self._domain.alphabet()]
        result = set()

        while wait:
            u = self(wait.pop())

            for i in xrange(len(u)-1):
                v = u[i:i+2]
                if v not in result:
                    result.add(v)
                    wait.append(v)

        return sorted(result)

    def is_train_track(self, proof=False):
        r"""
        Check wether ``self`` is train track (on the rose).

        A morphism is `train-track` if there is no cancellation between the
        images in the iteration of ``self``. If ``proof`` is set to ``True``
        then return a word also a word of length 2 in the attracting language of
        ``self`` such that there is a cancellation in its image under ``self``.

        EXAMPLES::


            sage: FreeGroupAutomorphism('a->ab, b->a').is_train_track()
            True
            sage: f = FreeGroupAutomorphism('a->c,b->bba,c->baDABebadABEbac,d->baDABebadAB,e->CABebadABEbac')
            sage: f.is_train_track()
            True

        Here is a simple non train track example::

            sage: f = FreeGroupAutomorphism('a->bcA,b->bcAca,c->a')
            sage: f.is_train_track()
            False
            sage: f.is_train_track(proof=True)
            (False, word: Ab)

        And one can check that the word Ab is in the attracting lamination::

            sage: f(f(f('a')))[12:14]
            Ab

        It is possible to obtain a train-track representative as follows::

            sage: tt = f.train_track()
            sage: tt.edge_map()
            WordMorphism: A->GA, B->FAGA, F->BG, G->F, a->AG, b->Agaf, f->bg, g->f
            sage: tt_aut = FreeGroupAutomorphism('a->AG,b->Agaf,f->bg,g->f')
            sage: tt_aut.is_train_track()
            True
        """
        A = self.domain().alphabet()
        L2 = self.length2_words()
        for u in self.length2_words():
            # TODO: the job is done twice
            u1 = self.image(u[0])
            u2 = self.image(u[1])
            if A.are_inverse(u1[-1],u2[0]):
                if proof:
                    return False, u
                return False

        if proof:
            return True, None
        return True

class FreeGroupAutomorphism(FreeGroupMorphism):
    """
    Free group automorphism.

    EXAMPLES::

        sage: FreeGroupAutomorphism("a->ab,b->ac,c->a")
        Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

        sage: F = FreeGroup('abc')
        sage: FreeGroupAutomorphism("a->ab,b->ac,c->a",F)
        Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

        sage: map = {'a': 'ab', 'b':'ac', 'c':'a'}
        sage: FreeGroupAutomorphism(map)
        Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version
    """
    def is_invertible(self):
        return True

    def __repr__(self):
        result="Automorphism of the %s: " %str(self._domain)
        result=result+"%s" %str(self)
        return result

    def __mul__(self, other):
        """
        Returns the composition self*other.
        """
        if isinstance(other,FreeGroupMorphism):
            m = dict((a,self(other.image(a))) for a in other.domain().alphabet().positive_letters())

            if isinstance(other,FreeGroupAutomorphism) or other.is_invertible():
                return FreeGroupAutomorphism(m,self.domain())

            return FreeGroupMorphism(m, self.domain())

        return WordMorphism.__mul__(self, other)

    def simple_outer_representative(self):
        """
        Shortest representative of the outer class of self.

        OUTPUT:

        A ``FreeGroupAutomorphism`` in the same outer class than ``self``.

        EXAMPLES::

            sage: phi=FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
            sage: phi.simple_outer_representative()
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
                        result[a]=result[a][1:]*Word([b])
                    elif result[a][-1]==B:
                        result[a]=Word([B])*result[a][:-1]
                    else:
                        result[a]=Word([B])*result[a]*Word([b])

        return FreeGroupAutomorphism(result,F)

    def rose_conjugacy_representative(self):
        """
        Topological representative of the conjugacy class of ``self``.

        SEE ALSO:

        This is the same as ``self.rose_representative()`` but the
        base graph of the ``TopologicalRepresentative`` is a
        ``GraphWithInverses`` instead of a ``MarkedGraph``.
        """
        from topological_representative import TopologicalRepresentative
        from inverse_graph import GraphWithInverses
        return TopologicalRepresentative(GraphWithInverses.rose_graph(self._domain.alphabet()),self)


    def rose_representative(self):
        """
        Topological representative on the rose on the alphabet.
        """
        from topological_representative import TopologicalRepresentative
        from marked_graph import MarkedGraph
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

        - If ``relative=False``, this topological representative is either
        an absolute train-track or fixes a subgraph (with a non
        contractible connected component).

        - If ``relative=True``, the output is a relative train-track

        - If ``stable=True``, the output is either a stable absolute
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

class free_group_automorphisms:
    r"""
    Many examples of free group automorphisms.
    """
    @staticmethod
    def tribonacci():
        """
        Tribonacci automorphism.
        """
        return FreeGroupAutomorphism("a->ab,b->ac,c->a",FreeGroup(3))

    @staticmethod
    def Handel_Mosher_inverse_with_same_lambda():
        """
        Example given in the introduction of [HM-parageometric].

        This is an iwip automorphisms that has the same expansion factor as its
        inverse: 3.199. It is not geometric and not parageometric.

        REFERECENCES:

        [HM-parageometric] M. Handel, L. Mosher, parageometric outer
        automorphisms of free groups, Transactions of
        Amer. Math. Soc. 359, 3153-3183, 2007.
        """
        F=FreeGroup(3)
        theta=pow(FreeGroupAutomorphism("a->b,b->c,c->Ba",F),4)
        psi=FreeGroupAutomorphism("a->b,b->a,c->c",F)
        return psi*theta*psi*theta.inverse()


    @staticmethod
    def Bestvina_Handel_example_1_1():
        """
        Automorphism given as Example 1.1 in [BH-train-track]

        REFERENCES:

        [BH-train-track] M. Bestvina, M.  Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.
        """
        return FreeGroupAutomorphism("a->b,b->c,c->d,d->ADBC",FreeGroup(4))

    @staticmethod
    def Bestvina_Handel_example_1_9():
        """
        Automorphism given as Example 1.9 in [BH-train-track]

        This automorphism cannot be represented by an absolute train-track. But
        the representation on the rose is a relative train-track.

        REFERENCES:

        [BH-train-track] M. Bestvina, M.  Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.
        """
        return FreeGroupAutomorphism("a->ba,b->bba,c->cAbaB",FreeGroup(3))

    @staticmethod
    def Bestvina_Handel_example_3_6():
        """
        Automorphism given as Example 3.6 in Bestvina, Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.

        This automorphism is train-track on the rose and has an indivisble
        Nielsen path in A.b which is inessential.

        REFERENCES:

        [BH-train-track] M. Bestvina, M.  Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.

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

        REFERENCES:

        [BH-train-track] M. Bestvina, M.  Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.

        """
        return FreeGroupAutomorphism("a->a,b->CAbac,c->CAbacacACABac",FreeGroup(3))

    @staticmethod
    def Handel_Mosher_axes_3_4():
        """
        Automorphism given in Section 3.4 of [HM-axes]

        This automorphism is iwip, not geometric and is train-track on
        the rose. It has expansion factor 4.0795. Its inverse is not
        train-track on the rose and has expansion factor 2.46557. It
        also appears in Section 5.5 of the paper.

        REFERENCES:

        [HM-axes] M. Handel, L. Mosher, axes
        in Outer space, Mem. Amer. Math. Soc. 213, 2011.

        """
        A = AlphabetWithInverses(['a','g','f'],['A','G','F'])
        return FreeGroupAutomorphism("a->afgfgf,f->fgf,g->gfafg",FreeGroup(A))

    @staticmethod
    def Handel_Mosher_axes_5_5():
        """
        Automorphism given in Section 5.5 of [HM-axes]

        This automorphism phi is iwip and not geometric. Both phi and
        phi.inverse() are train-track on the rose. phi has expansion
        factor 6.0329 while phi.inverse() has expansion factor
        4.49086.

        REFERENCES:

        [HM-axes] M. Handel, L. Mosher, axes
        in Outer space, Mem. Amer. Math. Soc. 213, 2011.

        """
        return FreeGroupAutomorphism("a->bacaaca,b->baca,c->caaca",FreeGroup(3))

    @staticmethod
    def Hilion_parabolic(k=1):
        """
        Automorphism given in Section 2 of [Hilion].

        This automorphism has a parabolic orbit inside F_4.

        REFERENCES:

        [Hilion] A. Hilion

        """
        F=FreeGroup(4)
        phi=FreeGroupAutomorphism("a->a,b->ba,c->caa,d->dc",F)
        if k>1:
            phi=phi*pow(F.dehn_twist(c,a),k-1)
        return phi

    @staticmethod
    def Handel_Mosher_parageometric_1():
        """
        Automorphism given in the introduction of [HM-parageometric]

        This automorphism phi is iwip, not geometric and
        parageometric. Both phi and phi.inverse() are train-track on
        the rose. phi has expansion factor 1.46557 while phi.inverse()
        has expansion factor 1.3247.

        REFERENCES:

        [HM-parageometric] M. Handel, L. Mosher, parageometric outer
        automorphisms of free groups, Transactions of
        Amer. Math. Soc. 359, 3153-3183, 2007.

        """
        return FreeGroupAutomorphism("a->ac,b->a,c->b",FreeGroup(3))

    @staticmethod
    def Cohen_Lustig_1_6():
        """

        Automorphism given as example 1.6 in [CL-dynamics].

        REFERENCES:

        [CL-dynamics] M. Cohen, M. Lustig, on the dynamics and the
        fixed subgroup of a free group automorphism, Inventiones
        Math. 96, 613-638, 1989.

        """
        return FreeGroupAutomorphism("a->cccaCCC,b->CaccAbC,c->accAbccaCCBaCCAccccACCC",FreeGroup(3))

    @staticmethod
    def Cohen_Lustig_7_2():
        """

        Automorphism given as example 7.2 in [CL-dynamics].

        REFERENCES:

        [CL-dynamics] M. Cohen, M. Lustig, on the dynamics and the
        fixed subgroup of a free group automorphism, Inventiones
        Math. 96, 613-638, 1989.


        """
        return FreeGroupAutomorphism("a->aabc,b->abc,c->abcc",FreeGroup(3))

    @staticmethod
    def Cohen_Lustig_7_3():
        """

        Automorphism given as example 7.3 in [CL-dynamics].

        REFERENCES:

        [CL-dynamics] M. Cohen, M. Lustig, on the dynamics and the
        fixed subgroup of a free group automorphism, Inventiones
        Math. 96, 613-638, 1989.

        """
        return FreeGroupAutomorphism("a->cabaa,b->baa,c->caba",FreeGroup(3))

    @staticmethod
    def Turner_Stallings():
        """
        Automorphism of F_4 given in [Turner].

        This automorphism comes from an idea of Stallings and although
        it is very short, it has a very long fixed word.

        REFERENCES:

        [Turner] ???

        """
        return FreeGroupAutomorphism("a->dac,b->CADac,c->CABac,d->CAbc",FreeGroup(4))
