# coding=utf-8
r"""
free_group_automorphism.py define FreeGroupMorphism, FreeGroupAutomorphism
and free_group_automorphisms class


AUTHORS:

- Thierry COULBOIS (2013-01-01): initial version
- Dominique BENIELLI (2016-02_15):
  AMU University <dominique.benielli@univ-amu.fr>, Integration in SageMath

EXAMPLES::
    sage: phi = FreeGroupAutomorphism('a->ab,b->A')
    sage: print phi
    a->ab,b->A
"""
# *****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# *****************************************************************************

from sage.combinat.words.morphism import WordMorphism
from free_group import FreeGroup, FreeGroupElement


class FreeGroupMorphism(object):
    def __init__(self, data, domain=None, codomain=None):
        r"""
        Construction of the morphism.

        EXAMPLES:

        1. If data is a str::

            sage: FreeGroupMorphism('a->ab,b->ba')
            FreeGroupMorphism: a->ab, b->ba
            sage: FreeGroupMorphism('a->ab,b->Ba')
            FreeGroupMorphism: a->ab, b->Ba
            sage: FreeGroupMorphism('a->a*b*c,b->b,c->a*b')
            FreeGroupMorphism: a->abc, b->bca, c->cab

        An erasing morphism::

            sage: FreeGroupMorphism('a->ab,b->')
            FreeGroupMorphism: a->ab, b->

        Use the arrows ('->') correctly::

            sage: FreeGroupMorphism('a->ab,b-')
            Traceback (most recent call last):
            ...
            ValueError: The second and third characters must be '->' (not '-')
            sage: FreeGroupMorphism('a->ab,b')
            Traceback (most recent call last):
            ...
            ValueError: The second and third characters must be '->' (not '')
            sage: FreeGroupMorphism('a->ab,a-]asdfa')
            Traceback (most recent call last):
            ...
            ValueError: The second and third characters must be '->' (not '-]')

        Each letter must be defined only once::

            sage: FreeGroupMorphism('a->ab,a->ba')
            Traceback (most recent call last):
            ...
            ValueError: The image of 'a' is defined twice.

        2. From a dictionary::

            sage: FreeGroupMorphism({"a":"ab","b":"ba"})
            FreeGroupMorphism: a->ab, b->ba
            sage: FreeGroupMorphism({'x0':['x0','X1','x0'],'x2':['x2','x2','x1']})

        3. From a FreeGroupMorphism::

            sage: FreeGroupMorphism(FreeGroupMorphism('a->ab,b->ba'))
            FreeGroupMorphism: a->ab, b->ba

        TESTS::

            sage: FreeGroupMorphism(',,,a->ab,,,b->ba,,')
            FreeGroupMorphism: a->ab, b->ba
        """
        if isinstance(data,FreeGroupMorphism):
            self._domain=data._domain
            self._codomain=data._codomain
            self._morph=data._morph
        elif isinstance(data, WordMorphism):
            if domain is None:
                domain = FreeGroup(data._domain.alphabet())
            self._domain = domain
            if codomain is None:
                co_alphabet = set(a.lower() for a in data._codomain.alphabet())
                codomain = FreeGroup(co_alphabet)
            self._codomain = codomain
            self._morph = dict()
            for a,im in data._morph.iteritems():
                a = self._domain(a)
                im = self._codomain(im)
                self._morph[a] = im
                self._morph[a.inverse()] = im.inverse()
        else:
            if isinstance(data, str):
                data = self._build_dict(data)
            elif not isinstance(data, dict):
                raise NotImplementedError

            if codomain is None:
                codomain = self._build_codomain(data)

            self._codomain = codomain

            if domain is None:
                domain = FreeGroup(sorted(data.keys()))

            self._domain = domain

            self._morph = {}

            for (key, val) in data.iteritems():
                key = domain(key)
                val = codomain(val)
                self._morph[key] = val
                self._morph[key.inverse()] = val.inverse()

    def _build_dict(self, s):
        r"""
        Parse the string input to FreeGroupMorphism and build the dictionary
        it represents.

        TESTS::

            sage: phi = FreeGroupMorphism('a->ab,b->ba')
            sage: phi._build_dict('a->ab,b->ba') == {'a': 'ab', 'b': 'ba'}
            True
            sage: phi._build_dict('a->ab,a->ba')
            Traceback (most recent call last):
            ...
            ValueError: The image of 'a' is defined twice.
            sage: phi._build_dict('a->ab,b>ba')
            Traceback (most recent call last):
            ...
            ValueError: The second and third characters must be '->' (not '>b')
        """
        tmp_dict = {}
        for fleche in s.split(','):
            if len(fleche) == 0:
                continue

            if len(fleche) < 3 or fleche[1:3] != '->':
                raise ValueError("The second and third characters must be '->' (not '%s')" % fleche[1:3])

            lettre = fleche[0]
            image = fleche[3:]

            if lettre in tmp_dict:
                raise ValueError("The image of %r is defined twice." % lettre)

            tmp_dict[lettre] = image
        return tmp_dict

    def _build_codomain(self, data):
        r"""
        Returns a FreeGroup containing all the letters in the images of
        ``data`` (which must be a dictionary).

        If upper case letter are present they are treated as inverses of
        the corresponding lower case letters.

        TESTS:

        If the image of all the letters are iterable::

            sage: phi = FreeGroupMorphism('a->ab,b->bA')
            sage: phi._build_codomain({'a': 'ab', 'b': 'bA'})
            FreeGroup on generators {a, b}
            sage: phi._build_codomain({'a': 'dcb', 'b': 'a'})
            FreeGroup on genrators {a, b, c, d}

        """
        codom_alphabet = set()
        for key, val in data.iteritems():
            for a in val:
                if isinstance(a,str):
                    a = a.lower()
                    codom_alphabet.add(a)
                else:
                    try:
                        codom_alphabet.update(a.parent().gens())
                    except AttributeError:
                        codom_alphabet.add(a)
        return FreeGroup(sorted(codom_alphabet))

    def __call__(self, w, order=1):
        """
        Apply the morphism to w.

        .. WARNING::

        if w is a letter of the alphabet which is iterable it will be
        considered as a word.

        EXAMPLES::

            sage: phi = FreeGroupMorphism('a->ab,b->aC,c->a')
            sage: phi('abC')
            a*b*a*c^-1*a^-1
            sage: phi(['a','B'],3)
            a*b*a*c^-1*a*b^2*c*a^-1*b^-1*a^-1
            sage: a = phi.domain().gen(0)
            sage: phi(a**-1)
            b^-1*a^-1
        """
        F = self.codomain()
        if not isinstance(w,FreeGroupElement):
            w = self.domain()(w)
        while order > 0:
            result = F.one()
            order = order - 1
            for a in w:
                result = result * self._morph[a]
            w = result
        return result

    def __mul__(self, other):
        """
         Returns the composition ``self`` o ``other``.

        INPUT:

        - ``other`` -- an other FreeGroupMorphism * by ``self``

        OUTPUT:

        The FreeGroupMorphism that is the composition ``self`` o ``other``.


        EXAMPLES::

            sage: phi = FreeGroupMorphism('a->ab,b->A')
            sage: psi = FreeGroupMorphism('a->aB,b->A')
            sage: phi * psi
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b*a,b->b^-1*a^-1
            sage: psi2 = WordMorphism('a->aB,b->A')
            sage: phi * psi2
            WordMorphism: a->aba, b->BA
            sage: psi3 =  FreeGroupMorphism('a->aB,b->A')
            sage: phi * psi3
            Morphism of the Free group over ['a', 'b']: a->aba,b->BA
        """
        morph = dict((a, self(other(a))) for a in other.domain().gens())
        return FreeGroupMorphism(morph, domain=other._domain, codomain=self._codomain)

    def __pow__(self, n):
        """
        INPUT:

        - ``n`` -- exponent for

        OUTPUT:

        returns self^n, where n is an integer.

        EXAMPLES::

            sage: phi = FreeGroupMorphism('a->ab,b->A')
            sage: phi**2
            Morphism from Free Group on generators {a, b} to Free Group on
            generators {a, b}: a->a*b*a^-1,b->b^-1*a^-1

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

        a string representation

        EXAMPLES::

            sage: phi = FreeGroupAutomorphism('a->ab,b->A')
            sage: phi.__str__()
            'a->ab,b->A'
            sage: print phi
            a->ab,b->A
        """
        result = ""
        for letter in self.domain().gens():
            result += str(letter) + "->" + str(self(letter)) + ","
        return result[:-1]

    def __repr__(self):
        """
        String representation.

        OUTPUT:

         a string representation

        EXAMPLES::

            sage: phi = FreeGroupMorphism('a->ab,b->A')
            sage: phi.__repr__()
            "Morphism of the Free group over ['a', 'b']: a->ab,b->A"
            sage: print phi
            a->ab,b->A
        """
        result = "Morphism from %s to %s: " %(str(self._domain),str(self._codomain))
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
            test = cmp(self(a), other(a))
            if test:
                return test
        return 0

    def domain(self):
        """
        Domain of ``self``. A FreeGroup.

        Returns:

        A FreeGroup.

        """
        return self._domain

    def codomain(self):
        """
        Codomain of ``self``. A FreeGroup.

        Returns:

        A FreeGroup.

        """
        return self._codomain

    def to_automorphism(self):
        """
        Automorphism defined by ``self``.

        OUTPUT:

        a FreeGroupAutomorphism

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

        a WordMorphism

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
        A=self.domain().gens()
        Anames = self.domain().variable_names()
        morph = dict((a,self(a).to_word()) for a in A)
        if forget_inverse:
            for key,value in morph.iteritems():
                for i,b in enumerate(value):
                    if b not in A:
                        value[i] = b**-1
            return WordMorphism(morph)

        for a,u in morph.iteritems():
            morph[a**-1] = u**-1

    def size(self):
        """
        Size of the endomorphism: half (floor) the maximum length of
        the image of a two letter word.

        OUTPUT:

        the size of ``self``

        EXAMPLES::

            sage: FreeGroupMorphism('a->abc,b->,c->ccc').size()
            3
        """
        result = 0
        A = self._domain.gens()
        A = A + tuple(a**-1 for a in A)
        for a in A:
            for b in A:
                if a != b**-1:
                    l = len(self(a) * self(b))
                    if result < l:
                        result = l
        return result // 2

    def is_permutation(self):
        """
        True if self is a permutation of the generators and their inverses
        of its domain.

        OUTPUT:

        True is 'self' is a permutaion

        EXAMPLES::

            sage: FreeGroupMorphism('a->a,b->b').is_permutation()
            True
            sage: FreeGroupMorphism('a->a,b->c,c->b').is_permutation()
            True
            sage: FreeGroupMorphism('a->A,b->c,c->b').is_permutation()
            True
            sage: FreeGroupMorphism('a->a,b->b,c->b').is_permutation()
            False
            sage: FreeGroupMorphism('a->a,b->ba').is_permutation()
            False
        """
        seen = set()
        for a in self._domain.gens():
            u=self(a)
            if len(u) != 1:
                return False
            if u in seen:
                return False
            seen.add(u)
            seen.add(u**-1)
        return True

    def _inverse_permutation(self):
        """
        Return the inverse of ``self`` if it is a permutation

        OUTPUT:

        FreeGroupAutomorphism inverse permutation

        EXAMPLES::

            sage: phi = FreeGroupMorphism('a->b,b->A')
            sage: phi._inverse_permutation()
            Automorphism of the Free Group on generators {a, b}: a->b^-1,b->a
        """
        F = self.domain()
        A = F.gens()
        result = {}
        for a in A:
            b = self(a)
            if b in A:
                result[b] = a
            else:
                result[b**-1] = a**-1

        return FreeGroupAutomorphism(result, domain=self._domain)

    def is_invertible(self):
        """
        ``True`` if ``self`` is an invertible morphism.

        OUTPUT:

            boolean

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
        try:
            self.inverse()
            return True
        except ValueError:
            return False

    def inverse(self):
        """
        Inverse of ``self`` computed with the Nielsen-Whitehead algorithm.


        Use Dehn twists to successively put ``self`` as identity and ``other``
         as the inverse of ``self``.

        OUTPUT:

        FreeGroupAutomorphism that is the inverse of ``self``


        EXAMPLES::

            sage: phi = FreeGroupAutomorphism("a->ab,b->ac,c->a")
            sage: phi.inverse()
            Automorphism of the Free group over ['a', 'b', 'c']: a->c,b->Ca,c->Cb

        ALGORITHM::

            Nielsen-Whitehead algorithm: search for a Nielsen elementary
            automorphism that reduces the size of the automorphism.

        """
        F = self._domain
        A = F.gens() + tuple(a**-1 for a in F.gens())

        other = FreeGroupAutomorphism.identity_automorphism(F)

        while True:
            # trivial case
            if self.is_permutation():
                return other * self._inverse_permutation()

            # the other one
            else:
                delta = -1

                for x in A:
                    wx = self(x)
                    for y in A:
                        if (x != y and x != y**-1):
                            wy = self(y)
                            wxy = wx * wy
                            l = len(wxy)
                            d = len(wx) - l
                            if d > delta:
                                if (d > 0):
                                    delta = d
                                    a = x
                                    b = y
                                else: # now d == 0
                                    if l == 1:
                                        if (wx < wxy):
                                            delta = 0
                                            a = x
                                            b = y
                                    else:
                                        half = (l + 1) // 2
                                        u1 = wxy[0:half]
                                        u2 = wxy[l-half:]**-1
                                        if u1 > u2:
                                            u1, u2 = u2, u1

                                        v1 = wx[0:half]
                                        v2 = wx[l-half:]**-1
                                        if v1 > v2:
                                            v1, v2 = v2, v1
                                        if (u1 < v1) or (u1 == v1 and u2 < v2):
                                            delta = 0
                                            a = x
                                            b =y

                if (delta == -1):
                    raise ValueError("%s is non invertible" % str(self))
                else:
                    na = FreeGroupAutomorphism.Nielsen_automorphism(F, a, b)
                    other = other * na
                    self = self * na



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

    def __init__(self,data,domain=None,codomain=None):
        """
        Build a FreeGroupAutomorphism.

        Args:
            data: anything from which an automorphism can be built
            domain: FreeGroup or None
            codomain: not used, for compatible reason with FreeGroupMorphism

        EXAMPLES::

            sage: FreeGroupAutomorphism("a->ab,b->ac,c->a")
            Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

            sage: F = FreeGroup('a,b,c')
            sage: FreeGroupAutomorphism("a->ab,b->ac,c->a",F)
            Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

            sage: map = {'a': 'ab', 'b':'ac', 'c':'a'}
            sage: FreeGroupAutomorphism(map)
            Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a

        """
        super(FreeGroupAutomorphism, self).__init__(data, domain=domain, codomain=domain)

    def is_invertible(self):
        """
        Test if ''self'' is invertible. Always ``True``.

        OUTPUT:

        ``True`` if ''self'' is invertible

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

        a string representation

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

        the composition self*other.

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

        m = dict((a, self(other(a))) for a in other.domain().gens())

        if isinstance(other, FreeGroupAutomorphism) or other.is_invertible():
            return FreeGroupAutomorphism(m, domain = self.domain())

        return FreeGroupMorphism(m, domain = other.domain(), codomain = self.codomain())


    def simple_outer_representative(self):
        """
        Shortest representative of the outer class of self.

        OUTPUT:

        a ``FreeGroupAutomorphism`` in the same outer
         class as ``self``.

        EXAMPLES::

            sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
            sage: phi.simple_outer_representative()
            Automorphism of the Free group over ['a', 'b', 'c']: a->ab,b->ac,c->a
        """
        F = self._domain
        A = F.gens()
        l = 2*len(A)
        result = dict(((a, self(a)) for a in A))
        done = False
        while not done:
            done = True
            gain = dict(((a, 0) for a in A))
            for a in A:
                gain[result[a][0]] += 1
                gain[result[a][-1]**-1] += 1
            for a in A:
                if gain[a] > l:
                    done = False
                    b = a
                    break
            if not done:
                bb = b**-1
                for a in A:
                    result[a] = bb * result[a] * b

        return FreeGroupAutomorphism(result, domain=F)

    def rose_conjugacy_representative(self):
        """
        Topological representative of the conjugacy class of ``self``.

        A Topological representative is a graph G together with a homotopy
        equivalence f: G->G such that the fundamental group of G is
        isomorphic to the domain of ``self`` and f and ``self`` commutes
        through this isomorphism. Note that as the isomorphism between the
        free group and the fundamental group of the graph is not specified,
        this depends on the conjugacy class of ``self``. Thus, the graph is
        just a graph (indeed a ``GraphWithInverses``) and not a
        ``MarkedGraph``.

        OUTPUT:

        A GraphSelfMap that is a topological representative of the
         conjugacy class of ``self``.

        EXAMPLES::

            sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
            sage: phi.rose_conjugacy_representative()

        SEE ALSO:

        This is the same as ``self.rose_representative()`` but the
        base graph of the ``GraphSelfMap`` is a
        ``GraphWithInverses`` instead of a ``MarkedGraph``.
        """
        from graph_self_map import GraphSelfMap
        from inverse_graph import GraphWithInverses
        from inverse_alphabet import AlphabetWithInverses

        A=AlphabetWithInverses(self._domain.gens())
        return GraphSelfMap(
            GraphWithInverses.rose_graph(A), self)


    def rose_representative(self):
        """
        ``GraphSelfMap``which is a topological representative of ``self``
        on the rose on the alphabet.

        OUTPUT:

        A topological representative of the
         conjugacy class of ``self``.

        EXAMPLES::

            sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
            sage: g = phi.rose_representative()
            sage: g.train_track()
            WordMorphism: A->eADE, B->eBE, C->DE, a->edaE, b->ebE, c->ed
        """
        from graph_self_map import GraphSelfMap
        from marked_graph import MarkedGraph
        from inverse_alphabet import AlphabetWithInverses

        F=self._domain
        A = self._domain.variable_names()
        for i in xrange(F.rank()):
            morph[A[i]] = self(F.gen(i)).to_word()
        A=AlphabetWithInverses(A)
        return GraphSelfMap(MarkedGraph.rose_marked_graph(A),self)

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

        A topological representative of self.


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

        ``True`` if ``self`` is an iwip automorphism.

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

        .. SEEALSO::

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
        """
        Returns the index list of ``self`` provided it is an iwip
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

        the FreeGroupAutomorphism  of the free group ``F``.

        EXAMPLES::

            sage: F = FreeGroup('a,b,c')
            sage: phi.identity_automorphism(F)
            Automorphism of the Free group over {'a', 'b', 'c'}: a->a,b->b,c->c
        """
        morph = dict((a, a) for a in F.gens())

        return FreeGroupAutomorphism(morph, domain=F)

    @staticmethod
    def Nielsen_automorphism(F, a, b, on_left=False):
        """
        Nielsen elementary automorphism of the free group ``F``.

        if ``on_left`` is ``False``: ``a -> ab``
        if ``on_left`` is ``True``: ``a -> ba``

        INPUT:

        - ``F`` -- a FreeGroup
        -  ``a``, ``b`` -- generators of F
        - ``on_left`` -- if ``on_left`` is ``False``: ``a -> ab``
                         if ``on_left`` is ``True``: ``a -> ba``

        OUTPUT:

        FreeGroupAutomorphism  of the free group ``F``.

        EXAMPLES::

            sage: F = FreeGroup('a,b,c')
            sage: FreeGroupAutomorphism.dehn_twist(F, 'a', 'b', on_left=True)
            Automorphism of the Free group over ['a', 'b', 'c']: a->ba,b->b,c->c

            sage: F=FreeGroup(3)
            sage: FreeGroupAutomorphism.dehn_twist(F,'a','c')
            Automorphism of the Free group over ['a', 'b', 'c']: a->ac,b->b,c->c
            sage: FreeGroupAutomorphism.dehn_twist(F,'A','c')
            Automorphism of the Free group over ['a', 'b', 'c']: a->Ca,b->b,c->c
        """

        if a in b or a**-1 in b:
            raise ValueError("%s must not appear in %s" % (str(a),str(b)))

        morph = dict((x, x) for x in F.gens())

        if a in F.gens():
            if on_left:
                morph[a] = b * a
            else:
                morph[a] = a * b
        else:
            a = a**-1
            if on_left:
                morph[a] = a * b**-1
            else:
                morph[a] = b**-1 * a

        return FreeGroupAutomorphism(morph,domain=F)

    @staticmethod
    def random_permutation(F):
        r"""
        Return an automorphism of the free group ``F`` that is induced by
        a random permutation  .

        INPUT:

        - ``F`` -- a FreeGroup

        OUTPUT:

        the FreeGroupAutomorphism  of the free group ``F`` with random
        permutation of its generators

        EXAMPLES::

            sage: F = FreeGroup('a,b,c')
            sage: FreeGroupAutomorphism.random_permutation(F).is_invertible()
            True
        """
        from sage.misc.prandom import randint
        from sage.groups.perm_gps.permgroup_named import SymmetricGroup

        A = F.gens()
        s = SymmetricGroup(P).random_element()
        f = {}
        for a in P:
            if randint(0, 1):
                f[a] = s(a)
            else:
                f[a] = s(a)**-1

        return FreeGroupAutomorphism(f, group=F)

    @staticmethod
    def random_automorphism(F, length=1):
        """
        Random automorphism of the free group ``F``.

        This is obtained by a random walk (without backtrack) on
        the automorphism group of ``F`` of ``length`` Dehn
        twist automorphisms.

        INPUT:

        - ``F`` -- a FreeGroup
        - ``lenght`` -- (default = 1) length of the random letters


        OUTPUT:

        the FreeGroupAutomorphism  of the free group ``F``.

        EXAMPLES::

            sage: F = FreeGroup('a,b,c')
            sage: FreeGroupAutomorphism.random_automorphism(F, length=2).is_invertible()
            True
        """
        if length == 0:
            return FreeGroupAutomorphism.identity_automorphism(F)

        A = F.gens()
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
        - ``k`` is an integer 0<=k<3g-1.


        OUTPUT:

        the FreeGroupAutomorphism
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
        """
        Automorphism of the free group ``F`` that is a random mapping class.

        This is obtained by a random walk of ``length`` using surface
        Dehn twists as generators without backtrack.

        INPUT:

        - ``F`` -- a FreeGroup
        - ``lenght`` -- (default = 1) length of the random letters
        - ``verbose`` -- ``True`` if ``self`` for the verbose option.

        OUTPUT:

        Automorphism of the free group ``F``
        that is a random mapping class

        EXAMPLES::

            sage: F = FreeGroup(4)
            sage: FreeGroupAutomorphism.random_mapping_class(F).__class__
            <class 'sage.combinat.words.free_group_automorphism.FreeGroupAutomorphism'>

        WARNING:

        The rank of ``F` is assumed to be even.

        ...SEE ALSO::

           :meth:`sage.combinat.words.fre_grop_automorphism.FreeGroupAutomorphism.surface_dehn_twist()`

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
        - ``i`` -- 0<i<n, where n is the rank of ``F``.
        - ``inverse`` -- default ``False`` If ``inverse`` is True returns
          the inverse of sigma_i.

        OUTPUT:

        Automorphism of the free group ``F`` which corresponds
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
        - ``lenght`` -- (default = 1) length of the random letters

        OUTPUT:

        A random braid automorphism of the free group ``F``.

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

        A Tribonacci automorphism.

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

        an iwip automorphisms that has the same expansion factor as its
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

        an iwip automorphisms and not geometric nor
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

        an automorphisms given as Example 1.9 in [BH-train-track]
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

        an automorphisms given as Example 3.6 in [BH-train-track]
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

        an automorphisms given as Example 3.6 in [BH-train-track]
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

        an automorphisms given in Section 3.4 of [HM-axes]
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

        an automorphisms given in Section 5.5 of [HM-axes]
        This automorphism phi is iwip and not geometric. Both phi and
        phi.inverse() are train-track on the rose. phi has expansion
        factor 6.0329 while phi.inverse() has expansion factor 4.49086.

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

        - ``k``  default value = 1

        OUTPUT:

        an automorphisms given in Section 2 of [Hilion].
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

        an automorphisms given in the introduction of
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

        an Automorphism given as example 1.6 in [CL-dynamics].
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

        an Automorphism given as example 7.2 in [CL-dynamics]..
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

        an Automorphism given as example 7.3 in [CL-dynamics].
        This is an atoroidal parageometric iwip.

        EXAMPLES::

            sage: free_group_automorphisms.Cohen_Lustig_7_3()
            Automorphism of the Free group over ['a', 'b', 'c']: a->cabaa,b->baa,c->caba

        REFERENCES:

        .. [CL-dynamics] M. Cohen, M. Lustig, on the dynamics and the
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

        an Automorphism of F_4 given in [Turner].
        This automorphism comes from an idea of Stallings and although
        it is very short, it has a very long fixed word.
        It is a reducible automorphism.

        EXAMPLES::

            sage: free_group_automorphisms.Turner_Stallings()
            Automorphism of the Free group over ['a', 'b', 'c', 'd']: a->dac,b->CADac,c->CABac,d->CAbc

        REFERENCES:

        .. [Turner] E. C. Turner, Finding indivisible Nielsen paths for a
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

        an Automorphism of F_4 given in [BH] see also [Kapovich].
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

        an Automorphism of F_3 given in Section 2 of [LL-periodic].
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

        an Automorphism of F_3 given in Section 2 of [CP-twisting].
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

        an Automorphism of F_4 suggested by
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

        an Automorphism of F_3 attributed to Shigeki Akiyama
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

        an Automorphism of F_4 suggested by Xavier Bressaud
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

        an Automorphism of F_4 suggested by Timo Jolivet [personal
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

        an Automorphism of F_3 given by M. Boshernitzan
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
