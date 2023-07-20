"""
FreeGroupMorphism, FreeGroupAutomorphism and free_group_automorphisms

free_group_automorphism.py defines FreeGroupMorphism, FreeGroupAutomorphism
and free_group_automorphisms class.


AUTHORS:

- Thierry COULBOIS (2013-01-01): initial version
- Dominique BENIELLI (2016-02_15):
  AMU University <dominique.benielli@univ-amu.fr>, Integration in SageMath

EXAMPLES::

    sage: from train_track import *
    sage: phi = FreeGroupAutomorphism('a->ab,b->A')
    sage: print(phi)
    a->a*b,b->a^-1

"""
# *****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# *****************************************************************************

from __future__ import print_function, absolute_import

import functools

from sage.combinat.words.morphism import WordMorphism
from .free_group import FreeGroup, FreeGroupElement

@functools.total_ordering
class FreeGroupMorphism(object):
    def __init__(self, data, domain=None, codomain=None):
        r"""
        Construction of the morphism.

        EXAMPLES:

        1. If data is a str::

            sage: from train_track import *
            sage: FreeGroupMorphism('a->ab,b->ba')
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b,b->b*a

            sage: FreeGroupMorphism('a->ab,b->Ba')
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b,b->b^-1*a

        An erasing morphism::

            sage: FreeGroupMorphism('a->ab,b->')
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b,b->1

        Use the arrows ('->') correctly::

            sage: FreeGroupMorphism('a->ab,b-')
            Traceback (most recent call last):
            ....
            ValueError: the sentence must have '->'

            sage: FreeGroupMorphism('a->ab,b')
            Traceback (most recent call last):
            ....
            ValueError: the sentence must have '->'

            sage: FreeGroupMorphism('a->ab,a-]asdfa')
            Traceback (most recent call last):
            ....
            ValueError: the sentence must have '->'

        Each letter must be defined only once::

            sage: FreeGroupMorphism('a->ab,a->ba')
            Traceback (most recent call last):
            ....
            ValueError: The image of 'a' is defined twice.

        2. From a dictionary::

            sage: FreeGroupMorphism({"a":"ab","b":"ba"})
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b,b->b*a
            sage: FreeGroupMorphism({'x0':['x0','X1','x0'],'x2':['x2','x2','x1']})
            Morphism from Free Group on generators {x0, x2} to Free Group on generators {x0, x1, x2}: x0->x0*x1^-1*x0,x2->x2^2*x1


        3. From a FreeGroupMorphism::

            sage: FreeGroupMorphism(FreeGroupMorphism('a->ab,b->ba'))
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b,b->b*a

        TESTS::

            sage: FreeGroupMorphism(',,,a->ab,,,b->ba,,')
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b,b->b*a
        """
        if isinstance(data, FreeGroupMorphism):
            self._domain=data._domain
            self._codomain=data._codomain
            self._morph=data._morph
        elif isinstance(data, WordMorphism):
            if domain is None:
                alphabet = set(a.lower() for a in data._domain.alphabet())
                domain = FreeGroup(alphabet)
            self._domain = domain
            if codomain is None:
                co_alphabet = set(a.lower() for a in data._codomain.alphabet())
                codomain = FreeGroup(co_alphabet)
            self._codomain = codomain
            self._morph = dict()
            for a,im in iter(data._morph.items()):
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

            for (key, val) in iter(data.items()):
                if isinstance(key, str):
                    key = domain([key])
                else:
                    key = domain(key)
                val = codomain(val)
                self._morph[key] = val
                self._morph[key.inverse()] = val.inverse()

    def _build_dict(self, s):
        r"""
        Parse the string input to FreeGroupMorphism and build the dictionary
        it represents.

        TESTS::

            sage: from train_track import *
            sage: phi = FreeGroupMorphism('a->ab,b->ba')
            sage: phi._build_dict('a->ab,b->ba') == {'a': 'ab', 'b': 'ba'}
            True
            sage: phi._build_dict('a->ab,a->ba') # doctest: +ELLIPSIS
            Traceback (most recent call last):
            ...
            ValueError: The image of 'a' is defined twice.

            sage: phi._build_dict('a->ab,b>ba')
            Traceback (most recent call last):
            ....
            ValueError: the sentence must have '->'
        """
        tmp_dict = {}
        for fleche in s.split(','):
            if len(fleche) == 0:
                continue
            if not fleche.__contains__('->'):
                raise ValueError("the sentence must have '->'")
            term = fleche.split('->')
            if len(term) == 0:
                raise ValueError("the sentence must have '->'")
            if len(term) >= 1:
                lettre = term[0]
                if len(term) >= 2:
                    image = term[1]
                else:
                    image = ''

            # if len(fleche) < 3 or fleche[1:3] != '->':
            #     raise ValueError("The second and third characters must be '->' (not '%s')" % fleche[1:3])
            #
            # lettre = fleche[0]
            # image = fleche[3:]
            #
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

            sage: from train_track import *
            sage: phi = FreeGroupMorphism('a->ab,b->bA')
            sage: phi._build_codomain({'a': 'ab', 'b': 'bA'})
            Free Group on generators {a, b}
            sage: phi._build_codomain({'a': 'dcb', 'b': 'a'})
            Free Group on generators {a, b, c, d}


        """
        codom_alphabet = set()
        for key, val in iter(data.items()):
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

            sage: from train_track import *
            sage: phi = FreeGroupMorphism('a->ab,b->aC,c->a')
            sage: phi('abC')
            a*b*a*c^-1*a^-1
            sage: phi(['a','B'],3)
            a*b*a*c^-1*a*b^2*c*a^-1*b^-1*a^-1
            sage: a = phi.domain().gen(0)
            sage: phi(a**-1)
            b^-1*a^-1
        """
        one = self.codomain().one()
        if not isinstance(w, FreeGroupElement):
            w = self.domain()(w)
        while order > 0:
            result = one
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

            sage: from train_track import *
            sage: phi = FreeGroupMorphism('a->ab,b->A')
            sage: psi = FreeGroupMorphism('a->aB,b->A')
            sage: phi * psi
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b*a,b->b^-1*a^-1
            sage: psi2 = WordMorphism('a->aB,b->A')
            sage: phi * psi2
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b*a,b->b^-1*a^-1

            sage: psi3 =  FreeGroupMorphism('a->aB,b->A')
            sage: phi * psi3
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b*a,b->b^-1*a^-1

        """
        if isinstance(other, WordMorphism):
            morph = {a: self(other(a)) for a in other._domain.alphabet()}
            dom =  FreeGroup(other._domain.alphabet())
        if isinstance(other, FreeGroupMorphism):
            morph = {a: self(other(a)) for a in other.domain().gens()}
            dom = other._domain
        return FreeGroupMorphism(morph, domain=dom, codomain=self._codomain)

    def __pow__(self, n):
        """
        INPUT:

        - ``n`` -- exponent for

        OUTPUT:

        returns self^n, where n is an integer.

        EXAMPLES::

            sage: from train_track import *
            sage: phi = FreeGroupMorphism('a->ab,b->A')
            sage: phi**2
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b*a^-1,b->b^-1*a^-1

        TESTS::

            sage: phi = FreeGroupAutomorphism('a->ab,b->A')
            sage: phi**-3
            Automorphism of the Free Group on generators {a, b}: a->b*a^-1*b^-1,b->b*a*b^-1*a^-1*b^-1
            sage: phi**0
            Automorphism of the Free Group on generators {a, b}: a->a,b->b

        """
        if n > 0:
            from sage.arith.power import generic_power
            return generic_power(self, n)
        elif n < 0:
            from sage.arith.power import generic_power

            return generic_power(self.inverse(), -n)
        else:
            return FreeGroupAutomorphism.identity_automorphism(self.domain())

    def __str__(self):
        """
        String representation.

        OUTPUT:

        a string representation

        EXAMPLES::

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism('a->ab,b->A')
            sage: phi.__str__()
            'a->a*b,b->a^-1'
            sage: print(phi)
            a->a*b,b->a^-1

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

            sage: from train_track import *
            sage: phi = FreeGroupMorphism('a->ab,b->A')
            sage: phi.__repr__()
            'Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b,b->a^-1'

            sage: print(phi)
            a->a*b,b->a^-1

        """
        return "Morphism from {} to {}: {}".format(self._domain, self._codomain, str(self))

    def __eq__(self, other):
        if type(self) is not type(other):
            return NotImplemented

        return self.domain() == other.domain() and \
               self.codomain() == other.codomain() and \
               all(self(a) == other(a) for a in self.domain().gens())

    def __lt__(self, other):
        """
        EXAMPLES::

            sage: from train_track import *
            sage: phi1 = FreeGroupMorphism('a->ab,b->A')
            sage: phi2 = FreeGroupMorphism('a->aba,b->Ab')
            sage: phi1 == phi2
            False
            sage: phi1 <= phi2
            True
        """
        if type(self) is not type(other):
            return NotImplemented

        if self.domain() != other.domain():
            return self.domain() < other.domain()
        if self.codomain() != other.codomain():
            return self.codomain() < other.codomain()

        for a in self.domain().gens():
            if self(a) != other(a):
                return self(a) < other(a)

        return False

    def domain(self):
        """
        Domain of ``self``. A FreeGroup.

        OUTPUT:

        A FreeGroup.

        EXAMPLES::

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism('a->ab,b->A')
            sage: phi.domain()
            Free Group on generators {a, b}

        """
        return self._domain

    def codomain(self):
        """
        Codomain of ``self``. A FreeGroup.

        OUTPUT:

        A FreeGroup.

        EXAMPLES::

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism('a->ab,b->A')
            sage: phi.codomain()
            Free Group on generators {a, b}

        """
        return self._codomain

    def to_automorphism(self):
        """
        Automorphism defined by ``self``.

        OUTPUT:

        a FreeGroupAutomorphism

        EXAMPLES::

            sage: from train_track import *
            sage: phi = FreeGroupMorphism('a->ab,b->A')
            sage: phi.to_automorphism()
            Automorphism of the Free Group on generators {a, b}: a->a*b,b->a^-1
        """
        if not self.is_invertible():
            raise ValueError("the morphism is not invertible")

        return FreeGroupAutomorphism(dict(
            (a, self._morph[a]) for a in self.domain().gens()))
        #,domain=self.domain())

    def to_word_morphism(self, use_str=False, upper_case_as_inverse=False, only_images_of_positive_letters=False, compact=False):
        r"""
        Return a word morphism.


        INPUT:

        - ``use_str`` -- (default: False) use ``str`` as letters (not FreeGroupElement)
        - ``upper_case_as_inverse`` -- (default: False) inverse of
          generators are translated to upper case ``str``
        - ``only_images_of_positive_letters`` -- (default: False) only positive letters
          have an image
        - ``compact`` -- (default: False) sets to True the three other options

        OUTPUT:

        A WordMorphism.

        .. NOTE::

            This method should not be there but on the other hand,
            f.periodic_points() fails for FreeGroupMorphism and
            FreeGroupAutomorphism

        EXAMPLES::

            sage: from train_track import *
            sage: f = FreeGroupAutomorphism('a->AD,b->Adac,c->bd,d->c')
            sage: f.to_word_morphism()
            WordMorphism: a->a^-1,d^-1, a^-1->da, b->a^-1,d,a,c, b^-1->c^-1,a^-1,d^-1,a, c->bd, c^-1->d^-1,b^-1, d->c, d^-1->c^-1
            sage: f.to_word_morphism().periodic_points()
            [[word: a^-1,d,a,c,c,c,a^-1,d^-1,d^-1,b^-1,d,a,c,a^-1,d^-1,b,d,b,d,b,d,d,a,c^-1,c^-1,c^-1,a^-1,d^-1,a,c,a^-1,d^-1,b,d,d,a,c^-1,a^-1,d,a,...,
              word: d,a,c,a^-1,d^-1,b,d,b,d,b,d,d,a,c^-1,c^-1,c^-1,a^-1,d^-1,a,c,a^-1,d^-1,b,d,d,a,c^-1,a^-1,d,a,c,c,a^-1,d,a,c,c,a^-1,d,a,...,
              word: c,a^-1,d^-1,b,d,d,a,c^-1,a^-1,d,a,c,c,a^-1,d,a,c,c,a^-1,d,a,c,c,c,a^-1,d^-1,d^-1,b^-1,d^-1,b^-1,d^-1,b^-1,d,a,c^-1,a^-1,d^-1,b,d,d,...,
              word: b,d,d,a,c^-1,a^-1,d,a,c,c,c,a^-1,d^-1,d^-1,b^-1,d,a,c,a^-1,d^-1,b,d,b,d,d,a,c,a^-1,d^-1,b,d,b,d,d,a,c,a^-1,d^-1,b,d,...],
             [word: c^-1,c^-1,a^-1,d^-1,a,c^-1,c^-1,a^-1,d^-1,a,c,a^-1,d^-1,d^-1,b^-1,d,a,c^-1,c^-1,c^-1,a^-1,d^-1,a,c^-1,c^-1,a^-1,d^-1,a,c,a^-1,d^-1,d^-1,b^-1,d,a,c^-1,a^-1,d,a,c,...,
              word: d^-1,b^-1,d^-1,b^-1,d,a,c^-1,a^-1,d^-1,d^-1,b^-1,d^-1,b^-1,d,a,c^-1,a^-1,d^-1,b,d,d,a,c^-1,c^-1,c^-1,a^-1,d^-1,a,c,a^-1,d^-1,d^-1,b^-1,d^-1,b^-1,d^-1,b^-1,d,a,c^-1,...]]
        """
        F = self._domain
        A = F.gens()

        if compact:
            use_str = True
            upper_case_as_inverse = True
            only_images_of_positive_letters = True
        
        if use_str:
            morph = dict((str(a),self(a).to_word(use_str=True,upper_case_as_inverse=upper_case_as_inverse)) for a in A)
            if not only_images_of_positive_letters:
                for a in A:
                    morph[str(a).upper()] = self(a**-1).to_word(use_str=True,upper_case_as_inverse=upper_case_as_inverse)
        else:
            morph = dict((a, self(a).to_word(use_str=False)) for a in A)
            if not only_images_of_positive_letters:
                for a in A:
                    morph[a**-1] = self(a).inverse().to_word(use_str=False)

        return WordMorphism(morph)

    def size(self):
        """
        Size of the endomorphism: half (floor) the maximum length of
        the image of a two letter word.

        OUTPUT:

        the size of ``self``

        EXAMPLES::

            sage: from train_track import *
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

            sage: from train_track import *
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

            sage: from train_track import *
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

            sage: from train_track import *
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

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism("a->ab,b->ac,c->a")
            sage: phi.inverse()
            Automorphism of the Free Group on generators {a, b, c}: a->c,b->c^-1*a,c->c^-1*b

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

        sage: from train_track import *
        sage: FreeGroupAutomorphism("a->ab,b->ac,c->a")
        Automorphism of the Free Group on generators {a, b, c}: a->a*b,b->a*c,c->a

        sage: F = FreeGroup('a,b,c')
        sage: FreeGroupAutomorphism("a->ab,b->ac,c->a", F)
        Automorphism of the Free Group on generators {a, b, c}: a->a*b,b->a*c,c->a
        sage: map = {'a': 'ab', 'b':'ac', 'c':'a'}
        sage: FreeGroupAutomorphism(map)
        Automorphism of the Free Group on generators {a, b, c}: a->a*b,b->a*c,c->a

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

            sage: from train_track import *
            sage: FreeGroupAutomorphism("a->ab,b->ac,c->a")
            Automorphism of the Free Group on generators {a, b, c}: a->a*b,b->a*c,c->a

            sage: F = FreeGroup('a,b,c')
            sage: FreeGroupAutomorphism("a->ab,b->ac,c->a",F)
            Automorphism of the Free Group on generators {a, b, c}: a->a*b,b->a*c,c->a
            sage: map = {'a': 'ab', 'b':'ac', 'c':'a'}
            sage: FreeGroupAutomorphism(map)
            Automorphism of the Free Group on generators {a, b, c}: a->a*b,b->a*c,c->a

        """
        super(FreeGroupAutomorphism, self).__init__(data, domain=domain, codomain=domain)

    def is_invertible(self):
        """
        Test if ''self'' is invertible. Always ``True``.

        OUTPUT:

        ``True`` if ''self'' is invertible

        EXAMPLES::

            sage: from train_track import *
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

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism('a->ab,b->A')
            sage: phi.__repr__()
            'Automorphism of the Free Group on generators {a, b}: a->a*b,b->a^-1'
            sage: print(phi)
            a->a*b,b->a^-1
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

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism('a->ab,b->A')
            sage: print(phi)
            a->a*b,b->a^-1
            sage: phi1 = FreeGroupAutomorphism('a->aB,b->A')
            sage: phi * phi1
            Automorphism of the Free Group on generators {a, b}: a->a*b*a,b->b^-1*a^-1
            sage: phi2 = WordMorphism('a->aB,b->A')
            sage: phi * phi2
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b*a,b->b^-1*a^-1
            sage: phi3 =  FreeGroupMorphism('a->aB,b->A')
            sage: phi * phi3
            Morphism from Free Group on generators {a, b} to Free Group on generators {a, b}: a->a*b*a,b->b^-1*a^-1

        """

        if isinstance(other, FreeGroupAutomorphism):
            m = dict((a, self(other(a))) for a in other.domain().gens())
            return FreeGroupAutomorphism(m, domain=self.domain())

        return FreeGroupMorphism.__mul__(self, other)


    def simple_outer_representative(self):
        """
        Shortest representative of the outer class of self.

        OUTPUT:

        a ``FreeGroupAutomorphism`` in the same outer
         class as ``self``.

        EXAMPLES::

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
            sage: phi.simple_outer_representative()
            Automorphism of the Free Group on generators {a, b, c}: a->c^-1*a*b*c,b->c^-1*a*c^2,c->c^-1*a*c

         """
        F = self._domain
        A = F.gens()
        Atot = list(A)
        for a in A:
            Atot.append(a**-1)
        l = 2*len(Atot)
        result = dict(((a, self(a)) for a in A))
        done = False
        while not done:
            done = True
            gain = dict(((a, 0) for a in Atot))
            for a in A:
                gain[result[a][0]] += 1
                gain[result[a][-1]**-1] += 1
            for a in Atot:
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

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
            sage: phi.rose_conjugacy_representative()
            Graph self map:
            a: 0->0, b: 0->0, c: 0->0
            Edge map: a->Cabc, b->Cacc, c->Cac

        .. SEEALSO::

            This is the same as ``self.rose_representative()`` but the
            base graph of the ``GraphSelfMap`` is a
            ``GraphWithInverses`` instead of a ``MarkedGraph``.
        """
        from .graph_self_map import GraphSelfMap
        from .inverse_graph import GraphWithInverses
        from .inverse_alphabet import AlphabetWithInverses

        A = AlphabetWithInverses(self._domain.variable_names())
        rose = GraphWithInverses.rose_graph(A)
        edge_map = dict((str(a), self(a).to_word()) for a in self._domain.gens())
        return GraphSelfMap(rose, edge_map)

    def rose_representative(self):
        """
        ``GraphSelfMap``which is a topological representative of ``self``
        on the rose on the alphabet.

        OUTPUT:

        A topological representative of the
         conjugacy class of ``self``.

        EXAMPLES::

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
            sage: g = phi.rose_representative()
            sage: g.train_track()
            WordMorphism: A->eADE, B->eBE, C->DE, a->edaE, b->ebE, c->ed
        """
        from .graph_self_map import GraphSelfMap
        from .marked_graph import MarkedGraph
        from .inverse_alphabet import AlphabetWithInverses

        A = AlphabetWithInverses(self._domain.variable_names())
        rose = MarkedGraph.rose_marked_graph(A)
        edge_map = dict((str(a), self(a).to_word()) for a in self._domain.gens())
        return GraphSelfMap(rose, edge_map)


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

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
            sage: g = phi.train_track()
            sage: print(g)
            Train-track map:
            Marked graph: a: 0->2, b: 2->2, d: 2->0, e: 0->2
            Marking: a->edaE, b->ebE, c->ed
            Edge map: a->bd, b->aded, d->a, e->d
            Irreducible representative
        """
        from .train_track_map import TrainTrackMap

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

            sage: from train_track import *
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

        6/ If there are two or more Nielsen loops then it is not iwip

        7/ If there is one Nielsen loop check whether it is contained in a
        non-trivial free factor.

        .. SEEALSO::

            :meth:`train_track.train_track_map.TrainTrackMap.is_iwip()`

        REFERENCES

        .. [Kapo-algo] I. Kapovich, Algorithmic detectability of iwip
           automorphisms, 2012, arXiv:1209.3732

        """
        from .train_track_map import TrainTrackMap

        f = self.train_track(stable=True, relative=False,
                             verbose=(verbose and verbose < 1 and verbose - 1))

        if verbose:
            print(f)

        if len(f._strata) > 1:
            if verbose:
                print("Reducible")
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

            sage: from train_track import *
            sage: phi = FreeGroupAutomorphism("a->Cabc,b->Cacc,c->Cac")
            sage: phi.index_list()
            [2, 2]

        REFERENCES:

        .. [HM-axes] M. Handel, L. Mosher, Axes in Outer Space, Memoirs
           AMS 1004, Amer Mathematical Society, 2011.

        .. WARNING::

            ``self`` is assumed to be iwip (or at least to
            have an expanding absolute train-track representative).

        """

        from .train_track_map import TrainTrackMap

        if verbose:
            print("Computing a train-track representative")
        f = self.train_track(relative=False, stable=False,
                             verbose=(verbose and verbose > 1 and verbose - 1))
        if f.is_train_track(verbose=(verbose and verbose > 1 and verbose - 1)):
            f = TrainTrackMap(f)
            return f.index_list(
                verbose=(verbose and verbose > 1 and verbose - 1))
        else:
            if verbose:
                print("self is not iwip, not implemented yet in this case")
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

            sage: from train_track import *
            sage: F = FreeGroup('a,b,c')
            sage: phi = FreeGroupAutomorphism('a->ab,b->A')
            sage: phi.identity_automorphism(F)
            Automorphism of the Free Group on generators {a, b, c}: a->a,b->b,c->c

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

            sage: from train_track import *
            sage: F = FreeGroup('a,b,c')
            sage: FreeGroupAutomorphism.Nielsen_automorphism(F, 'a', 'b', on_left=True)
            Automorphism of the Free Group on generators {a, b, c}: a->b*a,b->b,c->c

            sage: FreeGroupAutomorphism.Nielsen_automorphism(F,'A','c')
            Automorphism of the Free Group on generators {a, b, c}: a->c^-1*a,b->b,c->c
        """
        a = F(a)
        b = F(b)
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

        return FreeGroupAutomorphism(morph, domain=F)

    @staticmethod
    def random_permutation(F):
        r"""
        Return an automorphism of the free group ``F`` that is induced by
        a random permutation  .

        INPUT:

        - ``F`` -- a free group

        OUTPUT:

        The FreeGroupAutomorphism of the free group ``F`` with random
        permutation of its generators.

        EXAMPLES::

            sage: from train_track import *
            sage: F = FreeGroup('a,b,c')
            sage: FreeGroupAutomorphism.random_permutation(F).is_invertible()
            True
        """
        from sage.misc.prandom import randint
        from sage.groups.perm_gps.permgroup_named import SymmetricGroup

        A = F.gens()
        s = SymmetricGroup(A).random_element()
        f = {}
        for a in A:
            if randint(0, 1):
                f[a] = s(a)
            else:
                f[a] = s(a)**-1

        return FreeGroupAutomorphism(f, domain=F)

    @staticmethod
    def random_automorphism(F, length=1):
        """
        Random automorphism of the free group ``F``.

        This is obtained by a random walk (without backtrack) on
        the automorphism group of ``F`` of ``length`` Dehn
        twist automorphisms.

        INPUT:

        - ``F`` -- a :class:`FreeGroup`
        - ``lenght`` -- (default: 1) length of the random letters

        OUTPUT:

        the FreeGroupAutomorphism  of the free group ``F``.

        EXAMPLES::

            sage: from train_track import *
            sage: F = FreeGroup('a,b,c')
            sage: FreeGroupAutomorphism.random_automorphism(F, length=2).is_invertible()
            True
        """
        from sage.misc.prandom import randint

        if length == 0:
            return FreeGroupAutomorphism.identity_automorphism(F)

        l = F.rank()
        i = randint(1,l)
        side = randint(0,1)
        j = randint(-l,l-3)
        k = i + l * side + 2 * l * (j + l)   # 1 <= k <= 2l(2l-2)

        if j>=-i:
            j += 1
        if j>=0:
            j += 1
        if j>=i:
            j += 1   # -l <= j <= l and j!=0 and j!=i and j!=-i
        a = F([i])
        b = F([j])
        result = FreeGroupAutomorphism.Nielsen_automorphism(F, a, b, on_left=side)
        for i in range(length-1):
            new_k = randint(1, 2*l*(2*l-2)-1)
            if new_k>=k:
                new_k += 1

            k = new_k

            j = ((k - 1) // (2 * l)) - l
            i = k - 2 * l * (j +l)
            side = (i - 1) // l
            i = i - side * l

            if j >= -i:
                j += 1
            if j >= 0:
                j += 1
            if j >= i:
                j += 1

            result *= FreeGroupAutomorphism.Nielsen_automorphism(F, F([i]), F([j]), on_left=side)
        return result

    @staticmethod
    def _surface_dehn_twist_e(F, i):
        """
        TESTS::

            sage: from train_track import *
            sage: F = FreeGroup(4)
            sage: FreeGroupAutomorphism._surface_dehn_twist_e(F, i=0)
            Automorphism of the Free Group on generators {x0, x1, x2, x3}: x0->x1*x0,x1->x1,x2->x2,x3->x3
        """
        return FreeGroupAutomorphism.Nielsen_automorphism(F, F.gen(2 * i), F.gen(2 * i + 1), True)

    @staticmethod
    def _surface_dehn_twist_c(F, i):
        """
        TESTS::

            sage: from train_track import *
            sage: F = FreeGroup(4)
            sage: FreeGroupAutomorphism._surface_dehn_twist_c(F, i=0)
            Automorphism of the Free Group on generators {x0, x1, x2, x3}: x0->x0,x1->x2*x0^-1*x1,x2->x2,x3->x3*x0*x2^-1
        """
        result = {a: a for a in F.gens()}
        result[F.gen(2 * i + 1)] = F.gen(2 * i + 2) * (F.gen(2 * i)**-1) * F.gen(2 * i + 1)
        result[F.gen(2 * i + 3)] = F.gen(2 * i + 3) * F.gen(2 * i) * (F.gen(2 * i + 2)**-1)

        return FreeGroupAutomorphism(result, domain=F)

    @staticmethod
    def _surface_dehn_twist_m(F, i):
        """
        TESTS::

            sage: from train_track import *
            sage: F = FreeGroup(4)
            sage: FreeGroupAutomorphism._surface_dehn_twist_m(F, i=0)
            Automorphism of the Free Group on generators {x0, x1, x2, x3}: x0->x0,x1->x0*x1,x2->x0*x2*x0^-1,x3->x0*x3*x0^-1
        """

        result = {F.gen(j): F.gen(j) for j in range(2 * i +1)}

        a = F.gen(2 * i)
        aa = a**-1

        result[F.gen(2 * i + 1)] = a * F.gen(2 * i + 1)

        for j in range(2 * i + 2, F.rank()):
            result[F.gen(j)] = a * F.gen(j) * aa

        return FreeGroupAutomorphism(result, domain=F)

    @staticmethod
    def surface_dehn_twist(F, k):
        r"""
        Dehn twist of the surface (with one boundary component) with
        fundamental group the free group ``F``.

        The surface is assumed to have genus g and 1 boundary
        component. The fundamental group has rank `2g`, thus ``F`` is
        assumed to be of even rank.

        ``k`` is an integer `0 \leq k < 3g-1`.

        MCG(S_{g,1}) is generated by the Dehn twist along
        the curves:

        - `g` equators `e_i`,
        - `g` meridian `m_i`
        - `g-1` circles `c_i` around two consecutive 'holes'.

        for `0 \leq k < g` returns the Dehn twist along `e_i` with `i = k`

        for `g \leq k < 2g` returns the Dehn twist along `m_i` with `i = k-g`

        for `2g \leq k < 3g-1` returns the Dehn twist along `c_i`
        with `i = k-2g`

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
        - ``k`` -- an integer `0 \leq k < 3g-1`

        OUTPUT:

        The FreeGroupAutomorphism Dehn twist of the surface (with one
        boundary component) with fundamental group the free group ``F``.

        EXAMPLES::

            sage: from train_track import *
            sage: F = FreeGroup(4)
            sage: FreeGroupAutomorphism.surface_dehn_twist(F, k=0)
            Automorphism of the Free Group on generators {x0, x1, x2, x3}: x0->x1*x0,x1->x1,x2->x2,x3->x3

        .. WARNING::

            ``F`` is assumed to be of even rank.
        """
        assert F.rank() % 2 == 0

        g = F.rank() / 2
        if (0 <= k and k < g):
            return FreeGroupAutomorphism._surface_dehn_twist_e(F, k)
        elif (g <= k and k < 2 * g):
            return FreeGroupAutomorphism._surface_dehn_twist_m(F, k - g)
        elif (2 * g <= k and k < 3 * g - 1):
            return FreeGroupAutomorphism._surface_dehn_twist_c(F, k - 2 * g)


    @staticmethod
    def random_mapping_class(F, length=1, verbose=False):
        """
        Automorphism of the free group ``F`` that is a random mapping class.

        This is obtained by a random walk of ``length`` using surface
        Dehn twists as generators without backtrack.

        INPUT:

        - ``F`` -- a FreeGroup
        - ``lenght`` -- (default: 1) length of the random letters
        - ``verbose`` -- set to ``True`` for the verbose option

        OUTPUT:

        Automorphism of the free group ``F``
        that is a random mapping class.

        EXAMPLES::

            sage: from train_track import *
            sage: F = FreeGroup(4)
            sage: FreeGroupAutomorphism.random_mapping_class(F).__class__
            <class 'train_track.free_group_automorphism.FreeGroupAutomorphism'>

        .. WARNING:

            The rank of ``F` is assumed to be even.

        .. SEEALSO::

           :meth:`surface_dehn_twist()`
        """
        from sage.misc.prandom import randint

        assert F.rank() % 2 == 0

        if length == 0:
            return FreeGroupAutomorphism.identity_automorphism(F)

        r = 3 * F.rank() / 2 - 2
        i = randint(0, r)
        j = randint(0, 1)
        k = i + j * (r + 1)
        if j == 0:
            result = FreeGroupAutomorphism.surface_dehn_twist(F, i)
        else:
            result = FreeGroupAutomorphism.surface_dehn_twist(F, i)**-1
        if verbose:
            used_dehn_twists = [(i, 1 - 2 * j)]
        for ii in range(length - 1):
            new_k=randint(0,2*r)
            if k<=new_k:
                new_k += 1
            k = new_k
            if k > r:
                result = result * (FreeGroupAutomorphism.surface_dehn_twist(
                    F, k - r -1)**-1)
                if verbose:
                    used_dehn_twists.append((k - r - 1,-1))
            else:
                result = result * FreeGroupAutomorphism.surface_dehn_twist(
                    F, k)
                if verbose:
                    used_dehn_twists.append((k, 1))

        if verbose:
            print("List of surface Dehn twists used:",used_dehn_twists)

        return result

    @staticmethod
    def braid_automorphism(F, i, inverse=False):
        r"""
        Automorphism of the free group ``F`` which corresponds to the
        generator `\sigma_i` of the braid group.

        Let `F` be a free group. Then the braid group generator acts by

        .. MATH::

            \begin{aligned}
            \sigma_i: a_i & \mapsto a_i a_{i+1} a_i^{-1}
                   \\ a_j & \mapsto a_j \qquad (j \neq i).
            \end{aligned}

        We assume `0 < i < n`, where `n` is the rank of `F`.

        If ``inverse`` is True returns the inverse of sigma_i.

        INPUT:

        - ``F`` -- a :class:`FreeGroup`
        - ``i`` -- `0 < i < n`, where `n` is the rank of ``F``
        - ``inverse`` -- (default: ``False``) if ``inverse`` is ``True``,
          then return the inverse of `\sigma_i`

        OUTPUT:

        Automorphism of the free group ``F`` which corresponds
        to the generator sigma_i of the braid group

        EXAMPLES::

            sage: from train_track import *
            sage: F = FreeGroup('a,b,c,d')
            sage: FreeGroupAutomorphism.braid_automorphism(F, 2)
            Automorphism of the Free Group on generators {a, b, c, d}: a->a,b->b*c*b^-1,c->b,d->d
        """
        result = dict((a, a) for a in F.gens())
        if not inverse:
            a = F.gen(i-1)
            result[a] = a * F.gen(i) * (a**-1)
            result[F.gen(i)] = a
        else:
            a = F.gen(i)
            result[a] = (a**-1) * F.gen(i-1) * a
            result[F.gen(i - 1)] = a

        return FreeGroupAutomorphism(result,domain=F)

    @staticmethod
    def random_braid(F, length=1):
        """
        A random braid automorphism of the free group ``F``.

        This is obtained by a uniform random walk with generators
        given by ``braid_automorphism()`` without backtrack of length
        ``length``.

        INPUT:

        - ``F`` -- a :class:`FreeGroup`
        - ``lenght`` -- (default: 1) length of the random letters

        OUTPUT:

        A random braid automorphism of the free group ``F``.

        EXAMPLES::

            sage: from train_track import *
            sage: F = FreeGroup(4)
            sage: FreeGroupAutomorphism.random_braid(F).__class__
            <class 'train_track.free_group_automorphism.FreeGroupAutomorphism'>
        """
        from sage.misc.prandom import randint

        if length == 0:
            return FreeGroupAutomorphism.identity_automorphism(F)
        l = F.rank()
        i = randint(1, l - 1)
        j = randint(0, 1)
        k = i + (l - 1) * j
        result = FreeGroupAutomorphism.braid_automorphism(F, i, j != 0)
        for ii in range(length-1):
            new_k = randint(1, 2 * l - 3)
            if k < new_k:
                new_k += 1
            k = new_k
            if k >= l:
                result *= FreeGroupAutomorphism.braid_automorphism(F, k - l + 1, True)
            else:
                result *= FreeGroupAutomorphism.braid_automorphism(F, k, False)

        return result


class free_group_automorphisms:
    r"""
    Many examples of free group automorphisms.

    REFERENCES:

    .. [BH-train-track] M. Bestvina, M.  Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.

    .. [HM-parageometric] M. Handel, L. Mosher, parageometric outer
        automorphisms of free groups, Transactions of
        Amer. Math. Soc. 359, 3153-3183, 2007.

    .. [CL-dynamics] M. Cohen, M. Lustig, on the dynamics and the
        fixed subgroup of a free group automorphism, Inventiones
        Math. 96, 613-638, 1989.
    """
    @staticmethod
    def tribonacci():
        """
        Tribonacci automorphism.

        OUTPUT:

        A Tribonacci automorphism.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.tribonacci()
            Automorphism of the Free Group on generators {a, b, c}: a->a*b,b->a*c,c->a

        """
        return FreeGroupAutomorphism("a->ab,b->ac,c->a")

    @staticmethod
    def Handel_Mosher_inverse_with_same_lambda():
        """
        Example given in the introduction of [HM-parageometric]_.

        This is an iwip automorphisms that has the same expansion factor as its
        inverse: 3.199. It is not geometric and not parageometric.

        OUTPUT:

        An iwip automorphisms that has the same expansion factor as its
        inverse: 3.199. It is not geometric and not parageometric.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Handel_Mosher_inverse_with_same_lambda()
            Automorphism of the Free Group on generators {a, b, c}: a->b^-1*a*(c*a^-1)^2*b*c^-1*a*(b^-1*a*c)^2*a^-1*c*a^-1*b,b->b^-1*a*(c*a^-1)^2*b*c^-1*a*b^-1*a*c,c->b^-1*a*(c*a^-1)^2*b*c^-1*a
        """
        theta = pow(FreeGroupAutomorphism("a->b,b->c,c->Ba"), 4)
        psi = FreeGroupAutomorphism("a->b,b->a,c->c")
        return psi * theta * psi * theta.inverse()

    @staticmethod
    def Bestvina_Handel_train_track_1_1():
        """
        Automorphism given as Example 1.1 in [BH-train-track]_.

        This automorphism is iwip and not geometric nor
        parageometric. Its representative on the rose is
        train-track. Its inverse is also train-track on the rose.

        OUTPUT:

        An iwip automorphisms and not geometric nor
        parageometric. Its representative on the rose is
        train-track. Its inverse is also train-track on the rose.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Bestvina_Handel_train_track_1_1()
            Automorphism of the Free Group on generators {a, b, c, d}: a->b,b->c,c->d,d->a^-1*d^-1*b^-1*c^-1
        """
        return FreeGroupAutomorphism("a->b,b->c,c->d,d->ADBC")

    @staticmethod
    def Bestvina_Handel_train_track_1_9():
        """
        Automorphism given as Example 1.9 in [BH-train-track]_.

        This automorphism cannot be represented by an absolute train-track. But
        the representation on the rose is a relative train-track.

        OUTPUT:

        An automorphisms given as Example 1.9 in [BH-train-track]_.
        This automorphism cannot be represented by an absolute train-track.
        But the representation on the rose is a relative train-track.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Bestvina_Handel_train_track_1_9()
            Automorphism of the Free Group on generators {a, b, c}: a->b*a,b->b^2*a,c->c*a^-1*b*a*b^-1
        """
        return FreeGroupAutomorphism("a->ba,b->bba,c->cAbaB")

    @staticmethod
    def Bestvina_Handel_train_track_3_6():
        """
        Automorphism given as Example 3.6 in [BH-train-track].

        This automorphism is train-track on the rose and has an indivisble
        Nielsen path in A.b which is essential.

        OUTPUT:

        An automorphisms given as Example 3.6 in [BH-train-track]_.
        This automorphism is train-track on the rose and has an indivisble
        Nielsen path in A.b which is essential

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Bestvina_Handel_train_track_3_6()
            Automorphism of the Free Group on generators {a, b}: a->b*a,b->b^2*a
        """
        return FreeGroupAutomorphism("a->ba,b->bba")

    @staticmethod
    def Bestvina_Handel_train_track_5_16():
        """
        Automorphism given as Example 5.16 in [BH-train-track]_.

        This automorphism occurs as a pseudo-Anosov homeomorphism of
        the four-times punctured phere. Thus it is reducible.

        OUTPUT:

        An automorphisms given as Example 3.6 in [BH-train-track]_.
        This automorphism occurs as a pseudo-Anosov homeomorphism of
        the four-times punctured phere. Thus it is reducible.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Bestvina_Handel_train_track_5_16()
            Automorphism of the Free Group on generators {a, b, c}: a->a,b->c^-1*a^-1*b*a*c,c->c^-1*a^-1*b*(a*c)^2*a^-1*c^-1*a^-1*b^-1*a*c
        """
        return FreeGroupAutomorphism("a->a,b->CAbac,c->CAbacacACABac")

    @staticmethod
    def Handel_Mosher_axes_3_4():
        """
        Automorphism given in Section 3.4 of [HM-axes]_.

        This automorphism is iwip, not geometric and is train-track on
        the rose. It has expansion factor 4.0795. Its inverse is not
        train-track on the rose and has expansion factor 2.46557. It
        also appears in Section 5.5 of the paper.

        OUTPUT:

        An automorphisms given in Section 3.4 of [HM-axes]_.
        This automorphism is iwip, not geometric and is train-track on
        the rose. It has expansion factor 4.0795. Its inverse is not
        train-track on the rose and has expansion factor 2.46557. It
        also appears in Section 5.5 of the paper

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Handel_Mosher_axes_3_4()
            Automorphism of the Free Group on generators {a, f, g}: a->a*(f*g)^2*f,f->f*g*f,g->g*f*a*f*g
        """
        return FreeGroupAutomorphism("a->afgfgf,f->fgf,g->gfafg")

    @staticmethod
    def Handel_Mosher_axes_5_5():
        """
        Automorphism given in Section 5.5 of [HM-axes]_.

        This automorphism phi is iwip and not geometric. Both phi and
        phi.inverse() are train-track on the rose. phi has expansion
        factor 6.0329 while phi.inverse() has expansion factor
        4.49086.

        OUTPUT:

        An automorphisms given in Section 5.5 of [HM-axes]_.
        This automorphism phi is iwip and not geometric. Both phi and
        phi.inverse() are train-track on the rose. phi has expansion
        factor 6.0329 while phi.inverse() has expansion factor 4.49086.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Handel_Mosher_axes_5_5()
            Automorphism of the Free Group on generators {a, b, c}: a->b*(a*c*a)^2,b->b*a*c*a,c->c*a^2*c*a
        """
        return FreeGroupAutomorphism("a->bacaaca,b->baca,c->caaca")

    @staticmethod
    def Hilion_parabolic(k=1):
        """
        Automorphism given in Section 2 of [Hilion]_.

        This automorphism has a parabolic orbit inside `F_4`.

        INPUT:

        - ``k`` -- (default: 1) the parameter `k`

        OUTPUT:

        An automorphisms given in Section 2 of [Hilion].
        This automorphism has a parabolic orbit inside `F_4`.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Hilion_parabolic()
            Automorphism of the Free Group on generators {a, b, c, d}: a->a,b->b*a,c->c*a^2,d->d*c
            sage: free_group_automorphisms.Hilion_parabolic(k=3)
            Automorphism of the Free Group on generators {a, b, c, d}: a->a,b->b*a,c->c*a^4,d->d*c

        REFERENCES:

        .. [Hilion] A. Hilion, Dynamique des automorphismes des groupes
           libres, Thesis (Toulouse, 2004).
        """
        phi = FreeGroupAutomorphism("a->a,b->ba,c->caa,d->dc")
        F = phi.domain()
        if k > 1:
            phi = phi * pow(FreeGroupAutomorphism.Nielsen_automorphism(F, 'c', 'a'), k - 1)
        return phi

    @staticmethod
    def Handel_Mosher_parageometric_1():
        """
        Automorphism given in the introduction of [HM-parageometric]_.

        This automorphism phi is iwip, not geometric and
        parageometric. Both phi and phi.inverse() are train-track on
        the rose. phi has expansion factor 1.46557 while phi.inverse()
        has expansion factor 1.3247.

        OUTPUT:

        an automorphisms given in the introduction of
        [HM-parageometric]_.
        This automorphism phi is iwip, not geometric and
        parageometric. Both phi and phi.inverse() are train-track on
        the rose. phi has expansion factor 1.46557 while phi.inverse()
        has expansion factor 1.3247.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Handel_Mosher_parageometric_1()
            Automorphism of the Free Group on generators {a, b, c}: a->a*c,b->a,c->b

        """
        return FreeGroupAutomorphism("a->ac,b->a,c->b")

    @staticmethod
    def Cohen_Lustig_1_6():
        """
        Automorphism given as example 1.6 in [CL-dynamics]_.

        It is reducible.

        OUTPUT:

        An automorphism given as example 1.6 in [CL-dynamics]_.
        It is reducible.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Cohen_Lustig_1_6()
            Automorphism of the Free Group on generators {a, b, c}: a->c^3*a*c^-3,b->c^-1*a*c^2*a^-1*b*c^-1,c->a*c^2*a^-1*b*c^2*a*c^-2*b^-1*a*c^-2*a^-1*c^4*a^-1*c^-3
        """
        return FreeGroupAutomorphism("a->cccaCCC,b->CaccAbC,"
                                     "c->accAbccaCCBaCCAccccACCC")

    @staticmethod
    def Cohen_Lustig_7_2():
        """

        Automorphism given as example 7.2 in [CL-dynamics].

        this is an atoroidal iwip.

        OUTPUT:

        An automorphism given as example 7.2 in [CL-dynamics]_.
        This is an atoroidal iwip.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Cohen_Lustig_7_2()
            Automorphism of the Free Group on generators {a, b, c}: a->a^2*b*c,b->a*b*c,c->a*b*c^2
        """
        return FreeGroupAutomorphism("a->aabc,b->abc,c->abcc")

    @staticmethod
    def Cohen_Lustig_7_3():
        """
        Automorphism given as example 7.3 in [CL-dynamics]_.

        This is an atoroidal parageometric iwip.

        OUTPUT:

        An automorphism given as example 7.3 in [CL-dynamics]_.
        This is an atoroidal parageometric iwip.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Cohen_Lustig_7_3()
            Automorphism of the Free Group on generators {a, b, c}: a->c*a*b*a^2,b->b*a^2,c->c*a*b*a
        """
        return FreeGroupAutomorphism("a->cabaa,b->baa,c->caba")

    @staticmethod
    def Turner_Stallings():
        """
        Automorphism of `F_4` given in [Turner]_.

        This automorphism comes from an idea of Stallings and although
        it is very short, it has a very long fixed word.

        It is a reducible automorphism.

        OUTPUT:

        An automorphism of `F_4` given in [Turner]_.
        This automorphism comes from an idea of Stallings and although
        it is very short, it has a very long fixed word.
        It is a reducible automorphism.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Turner_Stallings()
            Automorphism of the Free Group on generators {a, b, c, d}: a->d*a*c,b->c^-1*a^-1*d^-1*a*c,c->c^-1*a^-1*b^-1*a*c,d->c^-1*a^-1*b*c

        REFERENCES:

        .. [Turner] E. C. Turner, Finding indivisible Nielsen paths for a
           train tracks map, Proc. of a work- shop held at Heriot-Watt Univ.,
           Edinburg, 1993 (Lond. Math. Soc. Lect. Note Ser., 204), Cambridge,
           Cambridge Univ. Press., 1995, 300-313.
        """
        return FreeGroupAutomorphism("a->dac,b->CADac,c->CABac,d->CAbc")

    @staticmethod
    def Bestvina_Handel_surface_homeo():
        """
        Automorphism of `F_4` given in [BH-train-track]_ see also [Kapovich]_.

        This is a pseudo-Anosov mapping class of the 5-punctured
        sphere. Thus this is not an iwip. However, its representative
        on the rose in train-track.

        OUTPUT:

        An automorphism of F_4 given in [BH-train-track]_ see also [Kapovich]_.
        This is a pseudo-Anosov mapping class of the 5-punctured
        sphere. Thus this is not an iwip. However, its representative
        on the rose in train-track.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Bestvina_Handel_surface_homeo()
            Automorphism of the Free Group on generators {a, b, c, d}: a->b,b->c,c->d*a^-1,d->d^-1*c^-1

        REFERENCES:

        .. [Kapovich] Ilya Kapovich, Algorithmic detectability of iwip
           automorphisms, arXiv:1209.3732
        """
        return FreeGroupAutomorphism("a->b,b->c,c->dA,d->DC")

    @staticmethod
    def Levitt_Lustig_periodic():
        """
        Automorphism of `F_3` given in Section 2 of [LL-periodic]_.

        This is an atoroidal iwip. It is positive and thus train-track
        on the rose.

        OUTPUT:

        An automorphism of `F_3` given in Section 2 of [LL-periodic]_.
        This is an atoroidal iwip. It is positive and thus train-track
        on the rose.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Levitt_Lustig_periodic()
            Automorphism of the Free Group on generators {a, b, c}: a->c*b,b->a,c->b*a

        REFERENCES:

        .. [LL-periodic] G. Levitt, and M. Lustig, Automorphisms of free
           groups have asymptotically periodic dynamics,

        """
        return FreeGroupAutomorphism("a->cb,b->a,c->ba")

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

            sage: from train_track import *
            sage: free_group_automorphisms.Clay_Pettet_twisting_out()
            Automorphism of the Free Group on generators {a, b, c}: a->b,b->c,c->a*b

        REFERENCES:

        .. [CP-twisting] M. Clay, and A. Pettet, Twisting out fully
           irreducible automorphisms, ArXiv:0906.4050

        """
        return FreeGroupAutomorphism("a->b,b->c,c->ab")

    @staticmethod
    def Hokkaido():
        """
        Automorphism of F_4 suggested by X. Bressaud [personal communication]

        Already studied by Thurston [reference needed]?

        This is a parageometric iwip.

        OUTPUT:

        An Automorphism of `F_4` suggested by
        X. Bressaud [personal communication].
        This is a parageometrix iwip.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Hokkaido()
            Automorphism of the Free Group on generators {a, b, c, d, e}: a->a*b,b->c,c->d,d->e,e->a

        REFERENCES:

        .. [Thurston] reference needed
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

        An automorphism of `F_3` attributed to Shigeki Akiyama
        by X. Bressaud.
        This is a non-geometric, non-parageometric atoroidal iwip. It
        is positive thus train-track on the rose.
        This is a Pisot substitution.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Akiyama()
            Automorphism of the Free Group on generators {a, b, c}: a->b,b->a*c,c->a

        REFERENCES:

        .. [Akiyama] reference needed
        """
        return FreeGroupAutomorphism("a->b,b->ac,c->a")

    @staticmethod
    def Bressaud():
        r"""
        Automorphism of `F_4` suggested by Xavier Bressaud
        [personal communication]

        It is positive thus train-track on the rose. This is a
        non-iwip automorphism.

        OUTPUT:

        An automorphism of `F_4` suggested by Xavier Bressaud
        [personal communication].
        It is positive thus train-track on the rose. This is a
        non-iwip automorphism.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Bressaud()
            Automorphism of the Free Group on generators {a, b, c, d}: a->d*b,b->d*c,c->d,d->a

        REFERENCES:

        reference needed
        """
        return FreeGroupAutomorphism("a->db,b->dc,c->d,d->a")

    @staticmethod
    def Jolivet():
        """
        Automorphism of `F_4` suggested by Timo Jolivet [personal
        communication].

        This is positive thus train-track on the rose. However it is
        not iwip as the ideal Whitehead graph at the sole vertex is
        not connected.

        This a geometric automorphism corresponding to a non-oriented
        pseudo-Anosov on the surface of genus 2 with 1 boundary
        component.

        OUTPUT:

        An automorphism of `F_4` suggested by Timo Jolivet [personal
        communication].

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Jolivet()
            Automorphism of the Free Group on generators {a, b, c, d}: a->d*b,b->d*c,c->d,d->a

        REFERENCES:

        reference needed
        """
        return FreeGroupAutomorphism("a->db,b->dc,c->d,d->a")

    @staticmethod
    def Boshernitzan_Kornfeld():
        r"""
        Automorphism of `F_3` given by M. Boshernitzan and M. Kornfeld [BK]_

        It is the induction of an interval translation mapping.

        This is the inverse of a parageometric iwip.

        OUTPUT:

        an Automorphism of `F_3` given by M. Boshernitzan
        and M. Kornfeld [BK]_
        It is the induction of an interval translation mapping.
        This is the inverse of a parageometric iwip.

        EXAMPLES::

            sage: from train_track import *
            sage: free_group_automorphisms.Boshernitzan_Kornfeld()
            Automorphism of the Free Group on generators {a, b, c}: a->b,b->c*a^3,c->c*a^2

        REFERENCES:

        .. [BK] M. Boshernitzan and M. Kornfeld, TODO
        """
        return FreeGroupAutomorphism("a->b,b->caaa,c->caa")

