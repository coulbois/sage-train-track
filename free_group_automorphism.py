# coding=utf-8
r"""
free_group_automorphism.py define FreeGroupMorphism, FreeGroupAutomorphism
and free_group_automorphisms class


AUTHORS:

- Thierry COULBOIS (2013-01-01): initial version

- Dominique BENIELLI (2016-02_15):
AMU University <dominique.benielli@univ-amu.fr>, Integration in SageMath

EXAMPLES::
sage: A = AlphabetWithInverses('ab')
sage: f = FreeGroup(A)
sage: Au = FreeGroupAutomorphism('a->ab,b->A')
sage: print Au
a->ab,b->A
sage: Au1 = FreeGroupAutomorphism('a->ab,b->A', f)
sage: print Au1
a->ab,b->A


"""
# *****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# *****************************************************************************
from inverse_alphabet import AlphabetWithInverses
from sage.combinat.words.morphism import WordMorphism
from free_group import FreeGroup


class FreeGroupMorphism(WordMorphism):
    def __init__(self, data, group=None):
        """
        Builds a FreeGroupMorphism from data.

        INPUT:

        - ``data`` -- the data used to build the morphism

        - ``group`` -- an optional free group

        EXAMPLES::
        sage: phi = FreeGroupMorphism('a->ab,b->A')
        sage: print phi
        a->ab,b->A
        sage: phi = FreeGroupMorphism('a->abc,b->Ac,c->C,d->ac')
        sage: A = AlphabetWithInverses('abcd')
        sage: F = FreeGroup(A)
        sage: phi = FreeGroupMorphism('a->abc,b->Ac,c->C,d->ac', F)
        sage: print phi
        a->abc,b->Ac,c->C,d->ac
        """
        if group is not None and not isinstance(group, FreeGroup):
            raise ValueError("the group must be a Free Group")

        WordMorphism.__init__(self, data)

        if group is None:
            A = AlphabetWithInverses(self.domain().alphabet())
            F = FreeGroup(A)
        else:
            F = group
            A = group.alphabet()

        self._domain = F
        self._codomain = F  # unuseful... consistency with WordMorphism
        for letter in self._morph.keys():
            self._morph[letter] = F(self._morph[letter]).reduced()
            self._morph[A.inverse_letter(letter)] = \
                self._morph[letter].inverse()

    def __call__(self, w, order=1):
        """
        Apply the morphism to the word w.

        .. WARNING::

        if w is a letter of the alphabet which is iterable
         it will be considered
        as a word. If you want the image of a letter use :meth:`image` instead.
        """
        F = self.codomain()
        while order > 0:
            result = F()
            order = order - 1
            for a in w:
                result = result * self.image(a)
            w = result
        return result

    def __mul__(self, other):
        """
         Returns the composition self*other.

        INPUT:
        - ``other`` -- an other FreeGroupMorphism * by 'self'

        OUTPUT:


        - Returns the composition self*other.
        a FreeGroupMorphism if 'other' is instance of FreeGroupMorphism
        else a WordMorphism

        EXAMPLES::
        sage: phi = FreeGroupMorphism('a->ab,b->A')
        sage: psi = FreeGroupMorphism('a->aB,b->A')
        sage: phi * psi
        Morphism of the Free group over ['a', 'b']: a->aba,b->BA
        sage: psi2 = WordMorphism('a->aB,b->A')
        sage: phi * psi2
        WordMorphism: a->aba, b->BA
        sage: psi3 =  FreeGroupMorphism('a->aB,b->A')
        sage: phi * psi3
        Morphism of the Free group over ['a', 'b']: a->aba,b->BA

        """
        if isinstance(other, FreeGroupMorphism):
            m = dict((a, self(other.image(a))) for a in
                     other.domain().alphabet().positive_letters())
            return FreeGroupMorphism(m, self.domain())
        return super(FreeGroupMorphism, self).__mul__(other)

    def __pow__(self, n):
        """
        INPUT:
        - ``n`` -- exponent for

        OUTPUT:

        - returns self^n, where n is an integer.

        EXAMPLES::

        sage: phi = FreeGroupMorphism('a->ab,b->A')
        sage: phi**2
        Morphism of the Free group over ['a', 'b']: a->abA,b->BA

        TESTS::

        sage: phi = FreeGroupAutomorphism('a->ab,b->A')
        sage: phi**-3
        Automorphism of the Free group over ['a', 'b']: a->bAB,b->baBAB
        sage: phi**0
        Automorphism of the Free group over ['a', 'b']: a->a,b->b

        """
        if n > 0:
            from sage.structure.element import generic_power
            return generic_power(self, n)
        elif n < 0:
            from sage.structure.element import generic_power

            return generic_power(self.inverse(), -n)
        else:
            return FreeGroupAutomorphism.identity_automorphism(self.domain())

    def __str__(self):
        """
        String representation.

        OUTPUT:
        - return a string representation

        EXAMPLES::
        sage: phi = FreeGroupAutomorphism('a->ab,b->A')
        sage: phi.__str__()
        'a->ab,b->A'
        sage: print phi
        a->ab,b->A

        """
        result = ""
        for letter in self.domain().alphabet().positive_letters():
            result += letter + "->"
            for a in self.image(letter):
                result += a
            result += ","
        return result[:-1]

    def __repr__(self):
        """
        String representation.

        OUTPUT:
        - return a string representation

        EXAMPLES::
        sage: phi = FreeGroupMorphism('a->ab,b->A')
        sage: phi.__repr__()
        "Morphism of the Free group over ['a', 'b']: a->ab,b->A"
        sage: print phi
        a->ab,b->A

        """
        result = "Morphism of the %s: " % str(self._domain)
        result = result + "%s" % str(self)
        return result

    def __cmp__(self, other):
        if not isinstance(other, FreeGroupMorphism):
            return cmp(self.__class__, other.__class__)
        if self.domain() != other.domain():
            return cmp(self.domain(), other.domain())
        if self.codomain() != other.codomain():
            return cmp(self.codomain(), other.codomain())

        for a in self.domain().alphabet().positive_letters():
            test = cmp(self.image(a), other.image(a))
            if test:
                return test
        return 0

    def to_automorphism(self):
        """
        Automorphism defined by `self`.

        OUTPUT:

        - a FreeGroupAutomorphism

        EXAMPLES::
        sage: phi = FreeGroupMorphism('a->ab,b->A')
        sage: phi.to_automorphism()
        Automorphism of the Free group over ['a', 'b']: a->ab,b->A

        """
        if not self.is_invertible():
            raise ValueError("the morphism is not invertible")
        return FreeGroupAutomorphism(dict(
            (a, self.image(a))
            for a in self.domain().alphabet().positive_letters()))
        #,domain=self.domain())

    def to_word_morphism(self, forget_inverse=False):
        r"""
        Return a word morphism.


        INPUT:
        - ``forget_inverse`` -- (default: False) forget the inverse or not.

        OUTPUT:
        - a WordMorphism

        .. NOTE::

            This method should not be there but on the other hand,
            f.periodic_points() fails for FreeGroupMorphism and
            FreeGroupAutomorphism

        EXAMPLES::

        sage: f = FreeGroupAutomorphism('a->AD,b->Adac,c->bd,d->c')
        sage: f.to_word_morphism()
        WordMorphism: A->da, B->CADa, C->DB, D->C, a->AD, b->Adac, c->bd, d->c
        sage: f.to_word_morphism().periodic_points()
            [[word: AdacccADDBdacADbdbdbddaCCCADacADbddaCAda...,
              word: dacADbdbdbddaCCCADacADbddaCAdaccAdaccAda...,
              word: cADbddaCAdaccAdaccAdacccADDBDBDBdaCADbdd...,
              word: bddaCAdacccADDBdacADbdbddacADbdbddacADbd...],
             [word: CCADaCCADacADDBdaCCCADaCCADacADDBdaCAdac...,
              word: DBDBdaCADDBDBdaCADbddaCCCADacADDBDBDBdaC...]]

        """
        if forget_inverse:
            A = self.domain().alphabet()
            f = {}
            for a in A.positive_letters():
                f[a] = map(A.to_positive_letter, self.image(a))
            return WordMorphism(f)

        return WordMorphism(dict((a, list(self.image(a)))
                                 for a in self.domain().alphabet()))

    def size(self):
        """
        Size of the endomorphism: half (floor) the maximum length of
        the image of a two letter word.

        OUTPUT:
        - return the size

        EXAMPLES::

        sage: FreeGroupMorphism('a->abc,b->,c->ccc').size()
        3
        """
        result = 0
        D = self.domain()
        A = self._domain._alphabet
        for a in A:
            for b in A:
                if not A.are_inverse(a, b):
                    l = (self.image(a) * self.image(b)).length()
                    if result < l:
                        result = l
        return result // 2

    def is_permutation(self):
        """
        True if self is a permutation of the alphabet.

        OUTPUT:

        - True is 'self' is permutaion

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
            if len(self.image(a)) != 1:
                return False
            b=self.image(a)[0]
            if b in seen:
                return False
            seen.add(b)
            seen.add(A.inverse_letter(b))
        return True

    def _inverse_permutation(self):
        """
        Return the inverse of ``self`` if it is a permutation

        OUTPUT:

        - FreeGroupAutomorphism  inverse permutation

        EXAMPLES::

        sage: FreeGroupMorphism('a->a,b->b')._inverse_permutation()
        Automorphism of the Free group over ['a', 'b']: a->a,b->b

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

        return FreeGroupAutomorphism(result, group=self._domain)

    def is_invertible(self):
        """
        Use Dehn twists successively to check wether ``self`` is invertible.

        OUTPUT:

        - True if 'self' is invertible

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
        F = self.domain()
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
                            w3 = w1 * w2
                            d = w3.nielsen_strictly_less(w1)
                            if (delta < d and d >= 0):
                                delta = d
                                a = x
                                b = y

                if (delta == -1):
                    return False

                f = f * FreeGroupAutomorphism.dehn_twist(F, a, b)

    def inverse(self):
        """
        inverse of ``self`` computed with the Nielsen-Whitehead algorithm.


        Use Dehn twists to successively put ``self`` as identity and ``other``
         as the inverse of ``self``.

        OUTPUT:

        - inverse FreeGroupAutomorphism 


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

        other = FreeGroupAutomorphism.identity_automorphism(F)

        while True:
            # trivial case
            if self.is_permutation():
                return other * self._inverse_permutation()

            # the other one
            else:
                delta = -1

                for x in A:
                    w1 = self.image(x)

                    for y in A:
                        if (x != y and x != A.inverse_letter(y)):
                            w2 = self.image(y)
                            w3 = w1 * w2
                            d = w3.nielsen_strictly_less(w1)
                            if (delta < d and d >= 0):
                                delta = d
                                a = x
                                b = y

                if (delta == -1):
                    raise ValueError("%s is non invertible" % str(self))
                else:
                    other = other * FreeGroupAutomorphism.dehn_twist(F, a, b)
                    self = self * FreeGroupAutomorphism.dehn_twist(F, a, b)

    def length2_words(self):
        r"""
        Return the words of length 2 in the attracting language of ``self``.

        If the morphism is everywhere growing (a weaker condition than iwip)
        then there is a well defined notion of attracting lamination. If it is
        not the case, the output of this method should not be used.

        OUTPUT:
        - return the words of length 2 in the attracting language of ``self`

        EXAMPLES::

        sage: f = FreeGroupMorphism('a->ab,b->a')
        sage: f.length2_words()
        [word: aa, word: ab, word: ba, word: AA, word: AB, word: BA]

        """
        D = self.domain()
        A = D.alphabet()
        assert D is self.codomain()
        wait = [D([a]) for a in self._domain.alphabet()]
        result = set()

        while wait:
            u = self(wait.pop())

            for i in xrange(len(u) - 1):
                v = u[i:i + 2]
                if v not in result:
                    result.add(v)
                    wait.append(v)

        return sorted(result)

    def is_train_track(self, proof=False):
        r"""
        Check wether ``self`` is train track (on the rose).

        A morphism is `train-track` if there is no cancellation between the
        images in the iteration of ``self``. If ``proof`` is set to ``True``
        then return a word also a word of length 2 in the attracting language
        of ``self`` such that there is a cancellation in its image under
        ``self``.
        INPUT:

        - ``proof`` -- (default: False) .

        OUTPUT:

        - return True if the  morphism is train-track

        EXAMPLES::

        sage: FreeGroupAutomorphism('a->ab,b->a').is_train_track()
        True
        sage: f = FreeGroupAutomorphism('a->c,b->bba,c->baDABebadABEbac,\
        d->baDABebadAB,e->CABebadABEbac')
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
        word: Ab

        It is possible to obtain a train-track representative as follows::

        sage: tt = f.train_track()
        sage: tt.edge_map()
        WordMorphism: A->ga, B->FAGa, F->GB, G->F, a->AG, b->Agaf, f->bg, g->f
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
            if A.are_inverse(u1[-1], u2[0]):
                if proof:
                    return False, u
                return False

        if proof:
            return True, None
        return True

    def is_orientable(self):
        r"""
        Check whether the attracting language of ``self`` is orientable or
        equivalently if the attracting lamination is orientable.

        OUTPUT:

        - return True if the  ''self'' is orientable

        EXAMPLES::

        Some train-track examples::

        sage: FreeGroupAutomorphism('a->ab,b->C,c->A').is_orientable()
        True
        sage: FreeGroupAutomorphism('a->bcc,b->a,c->CBa').is_orientable()
        True

        sage: FreeGroupAutomorphism('a->cAbc,b->bc,c->ACa').is_orientable()
        False

        We check a conjugate of Fibonacci (which is not train-track)::

        sage: FreeGroupAutomorphism('a->Babb,b->Bab').is_orientable()
        True

        .. TODO::

        For Thierry, perhaps you want to include the method directly on
        GraphMap ?
        """
        if self.is_train_track():
            A = self.domain().alphabet()
            f = self.to_word_morphism()
        else:
            tt = self.train_track()
            if not tt.is_train_track():
                raise ValueError("no train track representative for self")
            f = tt.edge_map()  # it is a word morphism!!!
            A = tt.domain().alphabet()

        # we first find a letter which occurs in its image
        g = f
        while True:
            for letter in A:
                if letter in g.image(letter):
                    break
            else:
                g *= self
                continue
            break

        # then we can start computing its connected component
        seen = set([letter])
        wait = [letter]

        while wait:
            a = wait.pop()
            for b in set(g.image(a)):
                if A.inverse_letter(b) in seen:
                    return False

                if b not in seen:
                    wait.append(b)
                    seen.add(b)

        return True

    def complete_return_words(self, letter):
        r"""
        Compute the set of return words on ``letter``.

        The complete return word on ``letter`` are the set of words of the
        attracting language of ``self`` that have exactly two occurrences of
        ``letter`` or its inverse at the begining and at the end.

        The morphism must be train-track and irreducible.

        INPUT:

        - ``letter`` -- input `letter`` to be returned

        OUTPUT:

        - return return words form a basis of the free groups

        EXAMPLES:

        It is well known that for Tribonacci and its flipped version,
        the return words form a basis of the free group. Hence there
        are 6 of them::

        sage: f = FreeGroupAutomorphism('a->ab,b->ac,c->a')
        sage: Ra = f.complete_return_words('a'); Ra
        {word: aa, word: aba, word: aca, word: AA, word: ABA, word: ACA}
        sage: Rb = f.complete_return_words('b'); Rb
        {word: baab, word: bab, word: bacab, word: BAAB, word: BAB, word: BACAB}
        sage: Rc = f.complete_return_words('c'); Rc
        {word: cabaabac,
         word: cababac,
         word: cabac,
         word: CABAABAC,
         word: CABABAC,
         word: CABAC}

        sage: f = FreeGroupAutomorphism('a->ab,b->ca,c->a')
        sage: [len(f.complete_return_words(letter)) for letter in 'abc']
        [6, 6, 6]

        In general, the number of return words can be much larger::

        sage: f = FreeGroupAutomorphism('a->cAbc,b->bc,c->ACa')
        sage: [len(f.complete_return_words(letter)) for letter in 'abc']
        [12, 12, 18]
        """
        if not self.is_train_track():
            raise ValueError("self must be train-track")

        # we first need to compute a power of self which is positive (all
        # letters appear in each image)

        A = self.domain().alphabet()
        f = self
        while True:
            for a in A:
                u = f.image(a)
                if any(b not in u and A.inverse_letter(b) not in u for b in A):
                    f *= self
                    break
            else:
                break

        inv_letter = A.inverse_letter(letter)

        # precompute the first and last occurrence of letter/inv_letter in
        # images as well as return words contained inside the images
        complete_return_words = set()
        first_and_last = {}
        for a in A.positive_letters():
            b = A.inverse_letter(a)
            u = f.image(a)
            i = 0
            while u[i] != letter and u[i] != inv_letter:
                i += 1
            first_and_last[a] = [i, None]
            first_and_last[b] = [None, len(u) - i - 1]

            j = i + 1
            while j < len(u):
                if u[j] == letter or u[j] == inv_letter:
                    r = u[i:j + 1]
                    complete_return_words.add(r)
                    complete_return_words.add(~r)
                    i = j
                j += 1

            first_and_last[a][1] = i
            first_and_last[b][0] = len(u) - i - 1

        for a0, a1 in self.length2_words():
            u0 = f.image(a0)
            u1 = f.image(a1)

            i = first_and_last[a0][1]
            j = first_and_last[a1][0]

            r = u0[i:] * u1[:j + 1]
            complete_return_words.add(r)
            complete_return_words.add(~r)

        return complete_return_words


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
        """
        test if ''self'' is invertible always true

        OUTPUT:

        - True if ''self'' is invertible

        EXAMPLES::
        sage: phi = FreeGroupAutomorphism('a->ab,b->A')
        sage: phi.is_invertible()
        True

        """
        return True

    def __repr__(self):
        """
        String representation.

        OUTPUT:
        - return a string representation

        EXAMPLES::
        sage: phi = FreeGroupAutomorphism('a->ab,b->A')
        sage: phi.__repr__()
        "Automorphism of the Free group over ['a', 'b']: a->ab,b->A"
        sage: print phi
        a->ab,b->A
        """
        result = "Automorphism of the %s: " % str(self._domain)
        result = result + "%s" % str(self)
        return result

    def __mul__(self, other):

        """
         Returns the composition self*other.

        INPUT:
        - ``other`` -- an other FreeGroupAutomorphism * by 'self'

        OUTPUT:

        - Returns the composition self*other.

        a FreeGroupAutomorphism if ``other`` is instance of FreeGroupAutomorphism
        else a WordMorphism

        EXAMPLES::
        sage: phi = FreeGroupAutomorphism('a->ab,b->A')
        sage: print phi
        a->ab,b->A
        sage: phi1 = FreeGroupAutomorphism('a->aB,b->A')
        sage: phi * phi1
        Automorphism of the Free group over ['a', 'b']: a->aba,b->BA
        sage: phi2 = WordMorphism('a->aB,b->A')
        sage: phi * phi2
        WordMorphism: a->aba, b->BA
        sage: phi3 =  FreeGroupMorphism('a->aB,b->A')
        sage: phi * phi3
        Automorphism of the Free group over ['a', 'b']: a->aba,b->BA

        """
        if isinstance(other, FreeGroupMorphism):
            m = dict((a, self(other.image(a)))
                     for a in other.domain().alphabet().positive_letters())

            if isinstance(other, FreeGroupAutomorphism) \
                    or other.is_invertible():
                return FreeGroupAutomorphism(m, self.domain())

            return FreeGroupMorphism(m, self.domain())

        return WordMorphism.__mul__(self, other)

    def simple_outer_representative(self):
        """
        Shortest representative of the outer class of self.

        OUTPUT:

        - a ``FreeGroupAutomorphism`` in the same outer
         class as ``self``.

        EXAMPLES::

        sage: phi=FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
        sage: phi.simple_outer_representative()
        Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

        """
        F = self._domain
        A = F._alphabet
        l = len(A)
        result = dict(((a, self.image(a)) for a in A.positive_letters()))
        done = False
        while not done:
            done = True
            gain = dict(((a, 0) for a in A))
            for a in A.positive_letters():
                gain[result[a][0]] += 1
                gain[A.inverse_letter(result[a][-1])] += 1
            for a in A:
                if gain[a] > l:
                    done = False
                    b = a
            if not done:
                B = A.inverse_letter(b)
                for a in A.positive_letters():
                    if result[a][0] == b and result[a][-1] == B:
                        result[a] = result[a][1:-1]
                    elif result[a][0] == b:
                        result[a] = result[a][1:] * F([b])
                    elif result[a][-1] == B:
                        result[a] = F([B]) * result[a][:-1]
                    else:
                        result[a] = F([B]) * result[a] * F([b])

        return FreeGroupAutomorphism(result, F)

    def rose_conjugacy_representative(self):
        """
        Topological representative of the conjugacy class of ``self``.

        OUTPUT:

        - return A topological representative of the
         conjugacy class of ``self``.

        EXAMPLES::

        sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
        sage: g = phi.rose_conjugacy_representative()
        sage: g.train_track()
        WordMorphism: A->eADE, B->eBE, C->DE, a->edaE, b->ebE, c->ed

        SEE ALSO:

        This is the same as ``self.rose_representative()`` but the
        base graph of the ``GraphSelfMap`` is a
        ``GraphWithInverses`` instead of a ``MarkedGraph``.
        """
        from graph_self_map import GraphSelfMap
        from inverse_graph import GraphWithInverses

        return GraphSelfMap(
            GraphWithInverses.rose_graph(self._domain.alphabet()), self)


    def rose_representative(self):
        """
        ``GraphSelfMap``which is a topological representative of ``self``
        on the rose on the alphabet.

        OUTPUT:

        - return A topological representative of the
         conjugacy class of ``self``.

        EXAMPLES::

        sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
        sage: g = phi.rose_representative()
        sage: g.train_track()
        WordMorphism: A->eADE, B->eBE, C->DE, a->edaE, b->ebE, c->ed
        """
        from graph_self_map import GraphSelfMap
        from marked_graph import MarkedGraph

        return GraphSelfMap(MarkedGraph.rose_marked_graph(self._domain.alphabet()),self)

    def train_track(self, stable=True, relative=True, verbose=False):
        """Computes a train-track representative of ``self``.

        According to the options computes a relative (or ends when
        finding a reduction) and/or stable (with at most one INP
        crossing each exponential stratum). ``verbose`` can be either True
        or a positive number giving details on the computations.

        INPUT:

        - ``stable`` -- (default = True). If ``stable=True``, the
          output is either a stable absolute train-track or a stable
          relative train-track (if relative=False)


        - ``relative``  -- (default = True)
         If ``relative=False``, this topological representative is either
        an absolute train-track or fixes a subgraph (with a non
        contractible connected component).
         If ``relative=True``, the output is either an absolute
          train-track or a relative train-track

        - ``verbose`` -- (default = False) ``True`` or a positive number.

        OUTPUT:

        - A topological representative of self.


        EXAMPLES::

        sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
        sage: g = phi.train_track()
        sage: print g
        Train-track map:
        Marked graph: a: 0->2, b: 2->2, d: 2->0, e: 0->2
        Marking: a->edaE, b->ebE, c->ed
        Edge map: a->bd, b->aded, d->a, e->d
        Irreducible representative

        """
        from train_track_map import TrainTrackMap

        f = self.rose_representative()
        f.train_track(verbose)
        if len(f._strata) == 1:
            f = TrainTrackMap(f)
            if stable:
                f.stabilize(verbose)
        if relative and len(f._strata) > 1:
            if stable:
                f.stable_relative_train_track(verbose)
            else:
                f.relative_train_track(verbose)
        return f

    def is_iwip(self, verbose=False):
        """
        ``True`` if ``self`` is an iwip automorphism.

        INPUT:

        - ``verbose``  -- (default = False) ``True`` or a positive number.

        OUTPUT:

        - ``True`` if ``self`` is an iwip automorphism.

        EXAMPLES::
        sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
        sage: phi.is_iwip()
        True

        ALGORITHM:

        0/ Look for a train-track representaive ``f`` for ``self``.

        1/ Try to reduce ``f`` (removing valence 1 or 2 vertices,
          invariant forests)

        2/ Check that the matrix has a power with strictly positive entries

        3/ Check the connectedness of local Whitehead graphs

        4/ Look for periodic Nielsen paths and periodic Nielsen loops.

        5/ If there are no periodic Nielsen loop then it is an
        atoroidal iwip [Kapo-algo]

        6/ If there is more than two Nielsen loops then it is not iwip

        7/ If there is one iwip check whether it is contained in a
        non-trivial free factor.

        SEE ALSO::

        TrainTrackMap.is_iwip()

        REFERENCES

        [Kapo-algo] I. Kapovich, Algorithmic detectability of iwip
        automorphisms, 2012, arXiv:1209.3732
        """
        from train_track_map import TrainTrackMap

        f = self.train_track(stable=True, relative=False,
                             verbose=(verbose and verbose < 1 and verbose - 1))

        if verbose:
            print f

        if len(f._strata) > 1:
            if verbose:
                print "Reducible"
            return False

        f = TrainTrackMap(f)

        return f.is_iwip(verbose)

    def index_list(self, verbose=False):
        """Returns the index list of ``self`` provided it is an iwip
        automorphism.

        The index list is the list of indices of non-isogredient
        automorphisms in the outer class of ``self``. The index of an
        automorphism being computed from the number of attracting
        fixed points in the boundary of the free group and the rank of
        the fixed subgroup.

        Some authors (Mosher, Pfaff), use -1/2 our index definition.

        Some authors (Gaboriau, Jaeger, Levitt, Lustig), use 1/2 our index
        definition

        INPUT:

        - ``verbose``  -- (default = 1False) ``True`` or a positive number.

        OUTPUT:

        -return index list if is_train_track or False

        EXAMPLES::
        sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
        sage: phi.index_list()
        [2, 2]

        REFERENCES:

        [GJLL] D. Gaboriau, A. Jaeger, G. Levitt, M. Lustig, An index
        for counting fixed points of automorphisms of free
        groups. Duke Math. J., 93(3):425-452, 1998.

        [HM-axes] M. Handel, L. Mosher, Axes in Outer Space, Memoirs
        AMS 1004, Amer Mathematical Society, 2011.

        [Pfaff] C. Pfaff, Out(F_3) Index realization, arXiv:1311.4490.


        WARNING: ``self`` is assumed to be iwip (or at least to
        have an expanding absolute train-track representative).

        """

        from train_track_map import TrainTrackMap

        f = self.train_track(relative=False, stable=False,
                             verbose=(verbose and verbose > 1 and verbose - 1))
        if f.is_train_track(verbose=(verbose and verbose > 1 and verbose - 1)):
            f = TrainTrackMap(f)
            return f.index_list(
                verbose=(verbose and verbose > 1 and verbose - 1))
        else:
            if verbose:
                print "self is not iwip, not implemented yet in this case"
        return False

    @staticmethod
    def identity_automorphism(F):
        """
        Identity automorphism of the free group ``F``.

        INPUT:

        - ``F`` -- a FreeGroup

        OUTPUT:

        -return the FreeGroupAutomorphism  of the free group ``F``.

        EXAMPLES::
        sage: F = FreeGroup('abc')
        sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
        sage: phi.identity_automorphism(F)
        Automorphism of the Free group over ['a', 'b', 'c']: a->a,b->b,c->c

        """
        morph = dict((a, F([a])) for a in F.alphabet().positive_letters())

        return FreeGroupAutomorphism(morph, group=F)

    @staticmethod
    def dehn_twist(F, a, b, on_left=False):
        """Dehn twist automorphism of the free group ``F``.

        Some authors would rather call this automorphism an elementary
        Nielsen automorphism.

        if ``on_left`` is ``False``: ``a -> ab``
        if ``on_left`` is ``True``: ``a -> ba``
        INPUT:
        - ``F`` -- a FreeGroup
        -  ``a`` -- letter on the
        -  ``b`` -- letter on the
        - ``on_left`` -- if ``on_left`` is ``False``: ``a -> ab``
                         if ``on_left`` is ``True``: ``a -> ba``

        OUTPUT:

        -return the FreeGroupAutomorphism  of the free group ``F``.

        EXAMPLES::
        sage: F = FreeGroup('abc')
        sage: FreeGroupAutomorphism.dehn_twist(F, 'a', 'b', on_left=True)
        Automorphism of the Free group over ['a', 'b', 'c']: a->ba,b->b,c->c

        sage: F=FreeGroup(3)
        sage: FreeGroupAutomorphism.dehn_twist(F,'a','c')
        Automorphism of the Free group over ['a', 'b', 'c']: a->ac,b->b,c->c
        sage: FreeGroupAutomorphism.dehn_twist(F,'A','c')
        Automorphism of the Free group over ['a', 'b', 'c']: a->Ca,b->b,c->c

        """
        A = F.alphabet()

        if a not in A:
            raise ValueError("Letter %s not in alphabet" % str(a))
        if b not in A:
            raise ValueError("Letter %s not in alphabet" % str(b))
        if a == b:
            raise ValueError("Letter a=%s should be different from b=%s"
                             % (str(a), str(b)))
        if A.are_inverse(a, b):
            raise ValueError("Letter a=%s should be different from the"
                             " inverse of b=%s" % (str(a), str(b)))

        morphism = dict((letter, F([letter]))
                        for letter in A.positive_letters())

        if A.is_positive_letter(a):
            if on_left:
                morphism[a] = F([b, a])
            else:
                morphism[a] = F([a, b])
        else:
            a = A.inverse_letter(a)
            b = A.inverse_letter(b)
            if on_left:
                morphism[a] = F([a, b])
            else:
                morphism[a] = F([b, a])

        return FreeGroupAutomorphism(morphism, group=F)

    @staticmethod
    def random_permutation(F):
        r"""
        Return an automorphism of the free group ``F`` that is induced by
        a random permutation  .

        INPUT:
        - ``F`` -- a FreeGroup

        OUTPUT:

        -return the FreeGroupAutomorphism  of the free group ``F`` with random
        pertubation of the letters of its alphabet

        EXAMPLES::
        sage: F = FreeGroup('abc')
        sage: FreeGroupAutomorphism.random_permutation(F).is_invertible()
        True

        """
        from sage.misc.prandom import randint
        from sage.groups.perm_gps.permgroup_named import SymmetricGroup

        A = F.alphabet()
        P = A.positive_letters()
        s = SymmetricGroup(P).random_element()
        f = {}
        for a in P:
            if randint(0, 1):
                f[a] = F([s(a)])
            else:
                f[a] = F([A.inverse_letter(s(a))])

        return FreeGroupAutomorphism(f, group=F)

    @staticmethod
    def random_automorphism(F, length=1):
        """
        Random automorphism of the free group ``F``.

        This is obtained by a random walk (without backtrack) on
         the automorphism group of
        ``F`` of ``length`` Dehn twist automorphisms.

        INPUT:
        - ``F`` -- a FreeGroup
        -  ``lenght`` -- (default = 1) length of the random letters


        OUTPUT:

        -return the FreeGroupAutomorphism  of the free group ``F``.

        EXAMPLES::
        sage: F = FreeGroup('abc')
        sage: FreeGroupAutomorphism.random_automorphism(F, length=2).is_invertible()
        True

        """
        if length == 0:
            return FreeGroupAutomorphism.identity_automorphism(F)

        A = F.alphabet()
        a = A.random_letter()
        b = A.random_letter([a, A.inverse_letter(a)])
        result = FreeGroupAutomorphism.dehn_twist(F, a, b)
        for i in xrange(length - 1):
            new_a = A.random_letter()
            if new_a == a:
                b = A.random_letter([a, A.inverse_letter(a),
                                     A.inverse_letter(b)])
            else:
                a = new_a
                b = A.random_letter([a, A.inverse_letter(a)])
            result *= FreeGroupAutomorphism.dehn_twist(F, a, b)
        return result

    @staticmethod
    def _surface_dehn_twist_e(F, i):
        A = F.alphabet()
        a = A[2 * i]
        b = A[2 * i + 1]
        return FreeGroupAutomorphism.dehn_twist(F, a, b, True)

    @staticmethod
    def _surface_dehn_twist_c(F, i):

        A = F.alphabet()
        result = dict((a, F([a])) for a in A.positive_letters())
        result[A[2 * i + 1]] = F([A[2 * i + 2],
                                  A.inverse_letter(A[2 * i]), A[2 * i + 1]])
        result[A[2 * i + 3]] = F([A[2 * i + 3], A[2 * i],
                                  A.inverse_letter(A[2 * i + 2])])

        return FreeGroupAutomorphism(result, group=F)

    @staticmethod
    def _surface_dehn_twist_m(F, i):
        A = F.alphabet()
        result = {}
        for j in xrange(2 * i + 1):
            result[A[j]] = F([A[j]])
        a = A[2 * i]

        result[A[2 * i + 1]] = F([a, A[2 * i + 1]])
        aa = A.inverse_letter(a)
        for j in xrange(2 * i + 2, len(A)):
            result[A[j]] = F([a, A[j], aa])

        return FreeGroupAutomorphism(result, group=F)

    @staticmethod
    def surface_dehn_twist(F, k):
        """
        Dehn twist of the surface (with one boundary component) with
        fundamental group the free group ``F``.

        The surface is assumed to have genus g and 1 boundary
        component. The fundamental group has rank 2g, thus ``F`` is
        assumed to be of even rank.

        ``k`` is an integer 0<=k<3g-1.

        MCG(S_{g,1}) is generated by the Dehn twist along
        the curves:

        - g equators e_i,

        - g meridian m_i

        - g-1 circles c_i around two consecutive 'holes'.

        for 0<=k<g returns the Dehn twist along e_i with i=k

        for g<=k<2g returns the Dehn twist along m_i with i=k-g

        for 2g<=k<3g-1 returns the Dehn twist along c_i with i=k-2g

        The fundamental group has 2g generators. We fix the base point
        on the boundary. The generators are:

        - g x_i that turns around the i-th hole

        - g y_i that goes inside the i-th hole

        T_{e_i}: x_j-> x_j, x_i->y_ix_i, y_j->y_j

        T_{m_i}: x_j->x_j, y_j->y_j, j<i
                 x_i->x_i, y_i->x_iy_i
                 x_j->x_ix_jx_i\inv, y_j->x_iy_jx_i\inv

        T_{c_i}: x_j->x_j, y_j->y_j, y_i->x_{i+1}x_i\inv y_i,
         y_{i+1}->y_{i+1}x_{i+1}x_i\inv

        INPUT:
        - ``F`` -- a FreeGroup
        -  ``k`` is an integer 0<=k<3g-1.


        OUTPUT:

        -return the FreeGroupAutomorphism
            Dehn twist of the surface (with one boundary component) with
        fundamental group the free group ``F``

        EXAMPLES::
        sage: F = FreeGroup(4)
        sage: FreeGroupAutomorphism.surface_dehn_twist(F, k=0)
        Automorphism of the Free group over ['a', 'b', 'c', 'd']: a->ba,b->b,c->c,d->d

        WARNING:

        ``F`` is assumed to be of even rank.

        """
        assert len(F._alphabet) % 2 == 0

        g = len(F._alphabet) / 2
        if (0 <= k and k < g):
            result = FreeGroupAutomorphism._surface_dehn_twist_e(F, k)
        elif (g <= k and k < 2 * g):
            result = FreeGroupAutomorphism._surface_dehn_twist_m(F, k - g)
        elif (2 * g <= k and k < 3 * g - 1):
            result = FreeGroupAutomorphism._surface_dehn_twist_c(F, k - 2 * g)

        return result

    @staticmethod
    def random_mapping_class(F, length=1, verbose=False):
        """Automorphism of the free group ``F`` that is a random mapping class.

        This is obtained by a random walk of ``length`` using surface
        Dehn twists as generators without backtrack.

        INPUT:
        - ``F`` -- a FreeGroup
        -  ``lenght`` -- (default = 1) length of the random letters
        - ``verbose`` -- ``True`` if ``self`` for the verbose option.

        OUTPUT:

        -return Automorphism of the free group ``F``
        that is a random mapping class

        EXAMPLES::
        sage: F = FreeGroup(4)
        sage: FreeGroupAutomorphism.random_mapping_class(F).__class__
        <class 'sage.combinat.words.free_group_automorphism.FreeGroupAutomorphism'>

        WARNING:

        The rank of ``F` is assumed to be even.

        SEE ALSO:

        FreeGroupAutomorphism.surface_dehn_twist()

        """
        from sage.misc.prandom import randint

        assert len(F.alphabet()) % 2 == 0

        if length == 0:
            return FreeGroupAutomorphism.identity_automorphism(F)

        r = 3 * len(F.alphabet()) / 2 - 2
        i = randint(0, r)
        j = randint(0, 1)
        if j == 0:
            result = FreeGroupAutomorphism.surface_dehn_twist(F, i)
        else:
            result = FreeGroupAutomorphism.surface_dehn_twist(F, i).inverse()
        used_dehn_twists = [(i, 1 - 2 * j)]
        for ii in xrange(length - 1):
            l = randint(0, 1)
            if j == l:
                i = randint(0, r)
            else:
                k = randint(0, r - 1)
                if k >= i: i = k + 1
                j = l
            if j == 0:
                result = result * FreeGroupAutomorphism.surface_dehn_twist(
                    F, i)
            else:
                result = result * FreeGroupAutomorphism.surface_dehn_twist(
                    F, i).inverse()
            used_dehn_twists.append((i, 1 - 2 * j))
        if verbose:
            print "List of surface Dehn twists used:",used_dehn_twists
        return result

    @staticmethod
    def braid_automorphism(F, i, inverse=False):
        """
        Automorphism of the free group ``F`` which corresponds to the generator
        sigma_i of the braid group.

        sigma_i: a_i -> a_i a_{i+1} a_i^{-1}
                 a_j -> a_j, for j!=i

        We assume 0<i<n, where n is the rank of ``F``.

        If ``inverse`` is True returns the inverse of sigma_i.


        INPUT:
        - ``F`` -- a FreeGroup
        -  ``i`` -- 0<i<n, where n is the rank of ``F``.
        - ``inverse`` -- default ``False`` If ``inverse`` is True returns
        the inverse of sigma_i.

        OUTPUT:

        -return Automorphism of the free group ``F`` which corresponds
        to the generator sigma_i of the braid group

        EXAMPLES::
        sage: F = FreeGroup(4)
        sage: FreeGroupAutomorphism.braid_automorphism(F, 2)
        Automorphism of the Free group over ['a', 'b', 'c', 'd']: a->a,b->bcB,c->b,d->d

        """
        A = F.alphabet()
        result = dict((a, F([a])) for a in A.positive_letters())
        if not inverse:
            a = A[i - 1]
            result[a] = F([a, A[i], A.inverse_letter(a)])
            result[A[i]] = F([a])
        else:
            a = A[i]
            result[a] = F([A.inverse_letter(a), A[i - 1], a])
            result[A[i - 1]] = F(a)

        return FreeGroupAutomorphism(result,group=F)

    @staticmethod
    def random_braid(F, length=1):
        """A random braid automorphism of the free group ``F``.

        This is obtained by a uniform random walk with generators
        given by ``braid_automorphism()`` without backtrack of length
        ``length``.

        INPUT:
        - ``F`` -- a FreeGroup
        -  ``lenght`` -- (default = 1) length of the random letters

        OUTPUT:

        -return A random braid automorphism of the free group ``F``.

        EXAMPLES::
        sage: F = FreeGroup(4)
        sage: FreeGroupAutomorphism.random_braid(F).__class__
        <class 'sage.combinat.words.free_group_automorphism.FreeGroupAutomorphism'>

        """
        from sage.misc.prandom import randint

        A = F._alphabet
        if length == 0:
            return FreeGroupAutomorphism.identity_automorphism(F)
        i = randint(1, len(A) - 1)
        j = randint(0, 1)
        result = FreeGroupAutomorphism.braid_automorphism(F, i, j != 0)
        for ii in xrange(length-1):
            l = randint(0, 1)
            if l == j:
                i = randint(1, len(A) - 1)
            else:
                k = randint(1, len(A) - 2)
                if j <= k:
                    i = k + 1
            result *= FreeGroupAutomorphism.braid_automorphism(F, i, j)
        return result


class free_group_automorphisms:
    r"""
    Many examples of free group automorphisms.
    """

    @staticmethod
    def tribonacci():
        """
        Tribonacci automorphism.


        OUTPUT:

        -return A Tribonacci automorphism.

        EXAMPLES::
        sage: free_group_automorphisms.tribonacci()
        Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

        """
        return FreeGroupAutomorphism("a->ab,b->ac,c->a", FreeGroup(3))

    @staticmethod
    def Handel_Mosher_inverse_with_same_lambda():
        """
        Example given in the introduction of [HM-parageometric].

        This is an iwip automorphisms that has the same expansion factor as its
        inverse: 3.199. It is not geometric and not parageometric.

        OUTPUT:

        -return an iwip automorphisms that has the same expansion factor as its
        inverse: 3.199. It is not geometric and not parageometric.

        EXAMPLES::

        sage: free_group_automorphisms.Handel_Mosher_inverse_with_same_lambda()
        Automorphism of the Free group over ['a', 'b', 'c']: a->BacAcAbCaBacBacAcAb,b->BacAcAbCaBac,c->BacAcAbCa


        REFERECENCES:

        [HM-parageometric] M. Handel, L. Mosher, parageometric outer
        automorphisms of free groups, Transactions of
        Amer. Math. Soc. 359, 3153-3183, 2007.
        """
        F = FreeGroup(3)
        theta = pow(FreeGroupAutomorphism("a->b,b->c,c->Ba", F), 4)
        psi = FreeGroupAutomorphism("a->b,b->a,c->c", F)
        return psi * theta * psi * theta.inverse()

    @staticmethod
    def Bestvina_Handel_train_track_1_1():
        """
        Automorphism given as Example 1.1 in [BH-train-track].

        This automorphism is iwip and not geometric nor
        parageometric. Its representative on the rose is
        train-track. Its inverse is also train-track on the rose.

        OUTPUT:

        -return an iwip automorphisms and not geometric nor
        parageometric.Its representative on the rose is
        train-track. Its inverse is also train-track on the rose.

        EXAMPLES::

        sage: free_group_automorphisms.Bestvina_Handel_train_track_1_1()
        Automorphism of the Free group over ['a', 'b', 'c', 'd']: a->b,b->c,c->d,d->ADBC

        REFERENCES:

        [BH-train-track] M. Bestvina, M.  Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.
        """
        return FreeGroupAutomorphism("a->b,b->c,c->d,d->ADBC", FreeGroup(4))

    @staticmethod
    def Bestvina_Handel_train_track_1_9():
        """
        Automorphism given as Example 1.9 in [BH-train-track]

        This automorphism cannot be represented by an absolute train-track. But
        the representation on the rose is a relative train-track.

        OUTPUT:

        -return an automorphisms given as Example 1.9 in [BH-train-track]
         This automorphism cannot be represented by an absolute train-track.
         But the representation on the rose is a relative train-track.

        EXAMPLES::

        sage: free_group_automorphisms.Bestvina_Handel_train_track_1_9()
        Automorphism of the Free group over ['a', 'b', 'c']: a->ba,b->bba,c->cAbaB

        REFERENCES:

        [BH-train-track] M. Bestvina, M.  Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.
        """
        return FreeGroupAutomorphism("a->ba,b->bba,c->cAbaB", FreeGroup(3))

    @staticmethod
    def Bestvina_Handel_train_track_3_6():
        """
        Automorphism given as Example 3.6 in [BH-train-track].

        This automorphism is train-track on the rose and has an indivisble
        Nielsen path in A.b which is essential.

        OUTPUT:

        -return an automorphisms given as Example 3.6 in [BH-train-track]
        This automorphism is train-track on the rose and has an indivisble
        Nielsen path in A.b which is essential

        EXAMPLES::

        sage: free_group_automorphisms.Bestvina_Handel_train_track_3_6()
        Automorphism of the Free group over ['a', 'b']: a->ba,b->bba

        REFERENCES:

        [BH-train-track] M. Bestvina, M.  Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.

        """
        return FreeGroupAutomorphism("a->ba,b->bba", FreeGroup(2))

    @staticmethod
    def Bestvina_Handel_train_track_5_16():
        """
        Automorphism given as Example 5.16 in [BH-train-track].

        This automorphism occurs as a pseudo-Anosov homeomorphism of
        the four-times punctured phere. Thus it is reducible.

        OUTPUT:

        -return an automorphisms given as Example 3.6 in [BH-train-track]
        This automorphism occurs as a pseudo-Anosov homeomorphism of
        the four-times punctured phere. Thus it is reducible.

        EXAMPLES::

        sage: free_group_automorphisms.Bestvina_Handel_train_track_5_16()
        Automorphism of the Free group over ['a', 'b', 'c']: a->a,b->CAbac,c->CAbacacACABac

        REFERENCES:

        [BH-train-track] M. Bestvina, M.  Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.

        """
        return FreeGroupAutomorphism("a->a,b->CAbac,c->CAbacacACABac",
                                     FreeGroup(3))

    @staticmethod
    def Handel_Mosher_axes_3_4():
        """
        Automorphism given in Section 3.4 of [HM-axes]

        This automorphism is iwip, not geometric and is train-track on
        the rose. It has expansion factor 4.0795. Its inverse is not
        train-track on the rose and has expansion factor 2.46557. It
        also appears in Section 5.5 of the paper.

        OUTPUT:

        -return an automorphisms given in Section 3.4 of [HM-axes]
         This automorphism is iwip, not geometric and is train-track on
         the rose. It has expansion factor 4.0795. Its inverse is not
         train-track on the rose and has expansion factor 2.46557. It
         also appears in Section 5.5 of the paper

        EXAMPLES::

        sage: free_group_automorphisms.Handel_Mosher_axes_3_4()
        Automorphism of the Free group over ['a', 'g', 'f']: a->afgfgf,g->gfafg,f->fgf

        REFERENCES:

        [HM-axes] M. Handel, L. Mosher, axes
        in Outer space, Mem. Amer. Math. Soc. 213, 2011.

        """
        A = AlphabetWithInverses(['a', 'g', 'f'], ['A', 'G', 'F'])
        return FreeGroupAutomorphism("a->afgfgf,f->fgf,g->gfafg", FreeGroup(A))

    @staticmethod
    def Handel_Mosher_axes_5_5():
        """
        Automorphism given in Section 5.5 of [HM-axes]

        This automorphism phi is iwip and not geometric. Both phi and
        phi.inverse() are train-track on the rose. phi has expansion
        factor 6.0329 while phi.inverse() has expansion factor
        4.49086.

        OUTPUT:

        -return an automorphisms given in Section 5.5 of [HM-axes]
         This automorphism phi is iwip and not geometric. Both phi and
         phi.inverse() are train-track on the rose. phi has expansion
         factor 6.0329 while phi.inverse() has expansion factor
         4.49086.

        EXAMPLES::

        sage: free_group_automorphisms.Handel_Mosher_axes_5_5()
        Automorphism of the Free group over ['a', 'b', 'c']: a->bacaaca,b->baca,c->caaca

        REFERENCES:

        [HM-axes] M. Handel, L. Mosher, axes
        in Outer space, Mem. Amer. Math. Soc. 213, 2011.

        """
        return FreeGroupAutomorphism("a->bacaaca,b->baca,c->caaca",
                                     FreeGroup(3))

    @staticmethod
    def Hilion_parabolic(k=1):
        """
        Automorphism given in Section 2 of [Hilion].

        This automorphism has a parabolic orbit inside F_4.

        INPUT:
        -  ``k``  default value =1

        OUTPUT:

        -return an automorphisms given in Section 2 of [Hilion].
         This automorphism has a parabolic orbit inside F_4.

        EXAMPLES::

        sage: free_group_automorphisms.Hilion_parabolic()
        Automorphism of the Free group over ['a', 'b', 'c', 'd']: a->a,b->ba,c->caa,d->dc
        sage: free_group_automorphisms.Hilion_parabolic(k=3)
        Automorphism of the Free group over ['a', 'b', 'c', 'd']: a->a,b->ba,c->caaaa,d->dc

        REFERENCES:

        [Hilion] A. Hilion, Dynamique des automorphismes des groupes
        libres, Thesis (Toulouse, 2004).

        """

        F = FreeGroup(4)
        phi = FreeGroupAutomorphism("a->a,b->ba,c->caa,d->dc", F)
        if k > 1:
            phi = phi * pow(FreeGroupAutomorphism.dehn_twist(F, 'c', 'a'), k - 1)
        return phi

    @staticmethod
    def Handel_Mosher_parageometric_1():
        """
        Automorphism given in the introduction of [HM-parageometric].

        This automorphism phi is iwip, not geometric and
        parageometric. Both phi and phi.inverse() are train-track on
        the rose. phi has expansion factor 1.46557 while phi.inverse()
        has expansion factor 1.3247.

        OUTPUT:

        -return an automorphisms given in the introduction of
        [HM-parageometric].
         This automorphism phi is iwip, not geometric and
        parageometric. Both phi and phi.inverse() are train-track on
        the rose. phi has expansion factor 1.46557 while phi.inverse()
        has expansion factor 1.3247.

        EXAMPLES::

        sage: free_group_automorphisms.Handel_Mosher_parageometric_1()
        Automorphism of the Free group over ['a', 'b', 'c']: a->ac,b->a,c->b

        REFERENCES:

        [HM-parageometric] M. Handel, L. Mosher, parageometric outer
        automorphisms of free groups, Transactions of
        Amer. Math. Soc. 359, 3153-3183, 2007.

        """
        return FreeGroupAutomorphism("a->ac,b->a,c->b", FreeGroup(3))

    @staticmethod
    def Cohen_Lustig_1_6():
        """

        Automorphism given as example 1.6 in [CL-dynamics].

        It is reducible.


        OUTPUT:

        -return an Automorphism given as example 1.6 in [CL-dynamics].
         It is reducible.

        EXAMPLES::

        sage: free_group_automorphisms.Cohen_Lustig_1_6()
        Automorphism of the Free group over ['a', 'b', 'c']: a->cccaCCC,b->CaccAbC,c->accAbccaCCBaCCAccccACCC

        REFERENCES:

        [CL-dynamics] M. Cohen, M. Lustig, on the dynamics and the
        fixed subgroup of a free group automorphism, Inventiones
        Math. 96, 613-638, 1989.

        """
        return FreeGroupAutomorphism("a->cccaCCC,b->CaccAbC,"
                                     "c->accAbccaCCBaCCAccccACCC",
                                     FreeGroup(3))

    @staticmethod
    def Cohen_Lustig_7_2():
        """

        Automorphism given as example 7.2 in [CL-dynamics].

        this is an atoroidal iwip.

        OUTPUT:

        -return an Automorphism given as example 7.2 in [CL-dynamics]..
          this is an atoroidal iwip.

        EXAMPLES::

        sage: free_group_automorphisms.Cohen_Lustig_7_2()
        Automorphism of the Free group over ['a', 'b', 'c']: a->aabc,b->abc,c->abcc

        REFERENCES:

        [CL-dynamics] M. Cohen, M. Lustig, on the dynamics and the
        fixed subgroup of a free group automorphism, Inventiones
        Math. 96, 613-638, 1989.


        """
        return FreeGroupAutomorphism("a->aabc,b->abc,c->abcc", FreeGroup(3))

    @staticmethod
    def Cohen_Lustig_7_3():
        """

        Automorphism given as example 7.3 in [CL-dynamics].

        This is an atoroidal parageometric iwip.

        OUTPUT:

        -return an Automorphism given as example 7.3 in [CL-dynamics].
          This is an atoroidal parageometric iwip.

        EXAMPLES::

        sage: free_group_automorphisms.Cohen_Lustig_7_3()
        Automorphism of the Free group over ['a', 'b', 'c']: a->cabaa,b->baa,c->caba

        REFERENCES:

        [CL-dynamics] M. Cohen, M. Lustig, on the dynamics and the
        fixed subgroup of a free group automorphism, Inventiones
        Math. 96, 613-638, 1989.

        """
        return FreeGroupAutomorphism("a->cabaa,b->baa,c->caba", FreeGroup(3))

    @staticmethod
    def Turner_Stallings():
        """
        Automorphism of F_4 given in [Turner].

        This automorphism comes from an idea of Stallings and although
        it is very short, it has a very long fixed word.

        It is a reducible automorphism.

        OUTPUT:

        -return an Automorphism of F_4 given in [Turner].
          This automorphism comes from an idea of Stallings and although
        it is very short, it has a very long fixed word.
        It is a reducible automorphism.

        EXAMPLES::

        sage: free_group_automorphisms.Turner_Stallings()
        Automorphism of the Free group over ['a', 'b', 'c', 'd']: a->dac,b->CADac,c->CABac,d->CAbc

        REFERENCES:

        [Turner] E. C. Turner, Finding indivisible Nielsen paths for a
        train tracks map, Proc. of a work- shop held at Heriot-Watt Univ.,
        Edinburg, 1993 (Lond. Math. Soc. Lect. Note Ser., 204), Cambridge,
        Cambridge Univ. Press., 1995, 300-313.
        """
        return FreeGroupAutomorphism("a->dac,b->CADac,c->CABac,d->CAbc",
                                     FreeGroup(4))

    @staticmethod
    def Bestvina_Handel_surface_homeo():
        """
        Automorphism of F_4 given in [BH] see also [Kapovich].

        This is a pseudo-Anosov mapping class of the 5-punctured
        sphere. Thus this is not an iwip. However, its representative
        on the rose in train-track.

        OUTPUT:

        -return an Automorphism of F_4 given in [BH] see also [Kapovich].
          This is a pseudo-Anosov mapping class of the 5-punctured
        sphere. Thus this is not an iwip. However, its representative
        on the rose in train-track.

        EXAMPLES::

        sage: free_group_automorphisms.Bestvina_Handel_surface_homeo()
        Automorphism of the Free group over ['a', 'b', 'c', 'd']: a->b,b->c,c->dA,d->DC

        REFERENCES:

        [BH] M. Bestvina, and M. Handel, Train-tracks for surface
        homeomorphisms. Topology 34 (1995), no. 1, 109-140

        [Kapovich] Ilya Kapovich, Algorithmic detectability of iwip
        automorphisms, arXiv:1209.3732

        """

        return FreeGroupAutomorphism("a->b,b->c,c->dA,d->DC", FreeGroup(4))

    @staticmethod
    def Levitt_Lustig_periodic():
        """
        Automorphism of F_3 given in Section 2 of [LL-periodic].

        This is an atoroidal iwip. It is positive and thus train-track
        on the rose.

        OUTPUT:

        -return an Automorphism of F_3 given in Section 2 of [LL-periodic].
          This is an atoroidal iwip. It is positive and thus train-track
        on the rose.

        EXAMPLES::

        sage: free_group_automorphisms.Levitt_Lustig_periodic()
        Automorphism of the Free group over ['a', 'b', 'c']: a->cb,b->a,c->ba

        REFERENCES:

        [LL-periodic] G. Levitt, and M. Lustig, Automorphisms of free
        groups have asymptotically periodic dynamics,

        """
        return FreeGroupAutomorphism("a->cb,b->a,c->ba", FreeGroup(3))

    @staticmethod
    def Clay_Pettet_twisting_out():
        """
        Automorphism of F_3 given in Section 2 of [CP-twisting].

        This is an atoroidal iwip. It is positive and thus train-track
        on the rose.

        OUTPUT:

        -return an Automorphism of F_3 given in Section 2 of [CP-twisting].
          This is an atoroidal iwip. It is positive and thus train-track
        on the rose.

        EXAMPLES::

        sage: free_group_automorphisms.Clay_Pettet_twisting_out()
        Automorphism of the Free group over ['a', 'b', 'c']: a->b,b->c,c->ab

        REFERENCES:

        [CP-twisting] M. Clay, and A. Pettet, Twisting out fully
        irreducible automorphisms, ArXiv:0906.4050

        """
        return FreeGroupAutomorphism("a->b,b->c,c->ab", FreeGroup(3))

    @staticmethod
    def Hokkaido():
        """
        Automorphism of F_4 suggested by X. Bressaud [personal communication]

        Already studied by Thurston [reference needed]?

        This is a parageometric iwip.

        OUTPUT:

        -return an Automorphism of F_4 suggested by
        X. Bressaud [personal communication]
        This is a parageometrix iwip.

        EXAMPLES::

        sage: free_group_automorphisms.Hokkaido()
        Automorphism of the Free group over ['a', 'b', 'c', 'd', 'e']: a->ab,b->c,c->d,d->e,e->a

        REFERENCES:

        [Thurston] reference needed
        """
        return FreeGroupAutomorphism("a->ab,b->c,c->d,d->e,e->a")

    @staticmethod
    def Akiyama():
        """
        Automorphism of F_3 attributed to Shigeki Akiyama by X. Bressaud.

        This is a non-geometric, non-parageometric atoroidal iwip. It
        is positive thus train-track on the rose.

        This is a Pisot substitution.

        OUTPUT:

        -return an Automorphism of F_3 attributed to Shigeki Akiyama
        by X. Bressaud.
        This is a non-geometric, non-parageometric atoroidal iwip. It
        is positive thus train-track on the rose.
        This is a Pisot substitution.

        EXAMPLES::

        sage: free_group_automorphisms.Akiyama()
        Automorphism of the Free group over ['a', 'b', 'c']: a->b,b->ac,c->a

        REFERENCES:

        [Akiyama] reference needed

        """

        return FreeGroupAutomorphism("a->b,b->ac,c->a")

    @staticmethod
    def Bressaud():
        """
        Automorphism of F_4 suggested by Xavier Bressaud
         [personal communication]

        It is positive thus train-track on the rose. This is a
        non-iwip automorphism.

        OUTPUT:

        -return an Automorphism of F_4 suggested by Xavier Bressaud
         [personal communication]
        It is positive thus train-track on the rose. This is a
        non-iwip automorphism.

        EXAMPLES::

        sage: free_group_automorphisms.Bressaud()
        Automorphism of the Free group over ['a', 'b', 'c', 'd']: a->db,b->dc,c->d,d->a

        REFERENCES:

        reference needed

        """

        return FreeGroupAutomorphism("a->db,b->dc,c->d,d->a")

    @staticmethod
    def Jolivet():
        """Automorphism of F_4 suggested by Timo Jolivet [personal
        communication]

        This is positive thus train-track on the rose. However it is
        not iwip as the ideal Whitehead graph at the sole vertex is
        not connected.

        This a geometric automorphism corresponding to a non-oriented
        pseudo-Anosov on the surface of genus 2 with 1 boundary
        component.

        OUTPUT:

        -return an Automorphism of F_4 suggested by Timo Jolivet [personal
        communication]

        EXAMPLES::

        sage: free_group_automorphisms.Jolivet()
        Automorphism of the Free group over ['a', 'b', 'c', 'd']: a->db,b->dc,c->d,d->a

        REFERENCES:

        reference needed

        """

        return FreeGroupAutomorphism("a->db,b->dc,c->d,d->a")

    @staticmethod
    def Boshernitzan_Kornfeld():
        r"""
        Automorphism of F_3 given by M. Boshernitzan and M. Kornfeld [BK]

        It is the induction of an interval translation mapping.

        This is the inverse of a parageometric iwip.

        OUTPUT:

        -return an Automorphism of F_3 given by M. Boshernitzan
        and M. Kornfeld [BK]
        It is the induction of an interval translation mapping.
        This is the inverse of a parageometric iwip.

        EXAMPLES::

        sage: free_group_automorphisms.Boshernitzan_Kornfeld()
        Automorphism of the Free group over ['a', 'b', 'c']: a->b,b->caaa,c->caa

        REFERENCES:

        [BK] M. Boshernitzan and M. Kornfeld, TODO
        """
        return FreeGroupAutomorphism("a->b,b->caaa,c->caa")
