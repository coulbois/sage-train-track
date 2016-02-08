#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#                     2016 Vincent Delecroix <vincent.delecroix@labri.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.misc.prandom import randint, choice
from sage.structure.sage_object import SageObject
from sage.structure.parent import Parent
from sage.categories.sets_cat import EmptySetError
from sage.rings.integer import Integer

def AlphabetWithInverses(arg1=None, arg2=None, type='abc'):
    r"""
    Build an alphabet with inverse letters.

    EXAMPLES::

        sage: AlphabetWithInverses(5, 'abc')
        Alphabet with inverses on ['a', 'b', 'c', 'd', 'e']
        sage: AlphabetWithInverses(4, 'x0')
        Alphabet with inverses on ['x0', 'x1', 'x2', 'x3']
    """
    if isinstance(arg1, (int,Integer)) and arg2 is not None:
        alphabet = arg1
        inverse = None
        type = arg2
    else:
        alphabet = arg1
        inverse = arg2

    if type == 'abc':
        return Alphabet_abc(alphabet, inverse)
    elif type == 'a0':
        return Alphabet_prefix('a', 'A', alphabet, inverse)
    elif type == 'x0':
        return Alphabet_prefix('x', 'X', alphabet, inverse)
    else:
        raise ValueError("unknown alphabet")

class DynamicIntegerSet:
    r"""
    A simple class to handle a (dynamic) finite set of integers.

    The two main operations are:

    - creation of a new element with the method ``new``

    - remove an element with ``release``

    EXAMPLES::

        sage: A = DynamicIntegerSet(13)
        sage: A
        Dynamical integer set [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
        sage: A[5]
        5
        sage: A[-2]
        11
        sage: A.release(7)
        sage: A.release(4)
        sage: A.release(12)
        sage: A
        Dynamical integer set [0, 1, 2, 3, 5, 6, 8, 9, 10, 11]
        sage: A.index(8)
        6
        sage: A[6]
        8
        sage: A.new()
        4
        sage: A.new()
        7
        sage: A.new()
        12
        sage: A.new()
        13
        sage: A
        Dynamical integer set [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

    TESTS::

        sage: A = DynamicIntegerSet(2)
        sage: A[0]
        0
        sage: A.release(0)
        sage: A[0]
        1
        sage: for i in [10,6,None,None,7,3,9,None,None,None,None,None]:
        ....:     print A.new(i),
        10 6 0 2 7 3 9 4 5 8 11 12
        sage: assert list(A) == range(13) and len(A) == 13
        sage: assert all(i in A for i in range(13))
        sage: assert all(A[A.index(i)] == i for i in A)
        sage: -1 in A or 13 in A or 'a' in A
        False

        sage: A.release(12); A.release(10); A.release(4); A.release(7)
        sage: assert len(A) == 9
        sage: assert all(i in A for i in A)
        sage: assert all(A[A.index(i)] == i for i in A)
        sage: 12 in A or 10 in A or 4 in A or 7 in A
        False

        sage: print A.new(), A.new(), A.new(), A.new()
        4 7 10 12
        sage: assert list(A) == range(13) and len(A) == 13
        sage: assert all(i in A for i in range(13))
        sage: assert all(A[A.index(i)] == i for i in A)
    """
    def __init__(self, n=0):
        n = int(n)
        assert n >= 0
        self._bitset = [1]*n
        self._first_unset = n
        self._n = n

    def __getitem__(self, key):
        if isinstance(key,slice):
            return self.list()[key]
        else:
            key = key.__index__()

            if key >= 0:
                i = 0
                while i < self._n and not self._bitset[i]:
                    i += 1
                j = 0
                while i < self._n:
                    j += self._bitset[i]
                    if j > key:
                        return i
                    i += 1
                raise IndexError("set index out of range")
            else:
                key = -key-1
                i = self._n-1
                j = 0
                while i >= 0 and j <= key:
                    j += self._bitset[i]
                    if j > key:
                        return i
                    i -= 1
                raise IndexError("set index out of range")

    def __contains__(self, i):
        try:
            i = i.__index__()
        except (AttributeError,TypeError):
            return False
        return 0 <= i < self._n and self._bitset[i]

    def __len__(self):
        return sum(self._bitset)

    def __iter__(self):
        return (i for i in range(self._n) if self._bitset[i])

    def __repr__(self):
        return "Dynamical integer set {}".format(list(self))

    def index(self, i):
        if i not in self:
            raise ValueError("{} not in the set".format(i))
        return sum(self._bitset[:i])

    def random_element(self, i):
        return self._bitset[randint(len(self))]

    def release(self, i):
        assert i < self._n and self._bitset[i]
        self._bitset[i] = 0
        self._first_unset = min(self._first_unset, i)

    def new(self, r=None):
        if r is None:
            r = self._first_unset

            if r != self._n:
                self._bitset[r] = 1
                rr = r+1

                while rr < self._n and self._bitset[rr]:
                    rr += 1

                self._first_unset = rr
            else:
                self._bitset.append(1)
                self._n += 1
                self._first_unset += 1

        else:
            r = int(r)
            assert r >= self._n or not self._bitset[r]
            if r >= self._n:
                self._bitset.extend([0]*(r - self._n))
                self._bitset.append(1)
                self._n = r+1
            else:
                self._bitset[r] = 1

            if r == self._first_unset:
                rr = r + 1
                while rr < self._n and self._bitset[rr]:
                    rr += 1
                self._first_unset = rr

        return r

class AbstractAlphabetWithInverses(Parent):
    """
    (Abstract) class for alphabet with inverse letters.

    Intended to be used by FreeGroup.  Builds a finite ordered alphabet with an
    inverse for each letter. There must be no duplicate.

    Concrete implementations must contain the following methods:

    - ``_unrank_letter(self, i)``
    - ``_unrank_inverse_letter(self,i)``
    - ``_rank_letter(self, letter)``
    - ``is_positive_letter(self, letter)``
    - ``is_negative_letter(self,letter)``
    - ``copy``

    EXAMPLES::

        sage: AlphabetWithInverses(['a','b','c'],['A','B','C'])
        Alphabet with inverses on ['a', 'b', 'c']

        sage: AlphabetWithInverses(['a','b','c'])
        Alphabet with inverses on ['a', 'b', 'c']

        sage: AlphabetWithInverses(3)
        Alphabet with inverses on ['a', 'b', 'c']

        sage: AlphabetWithInverses(3, 'x0')
        Alphabet with inverses on ['x0', 'x1', 'x2']

    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version

    """
    def __init__(self, alphabet, inverse=None):
        """
        Builds a finite ordered alphabet with an inverse for each
        letter. There must be no duplicate. Inverse letters are either
        given or computed by capitalization.

        The alphabet can also be specified by the number of letters
        and its type (default is 'abc'). `

        INPUT:

        ``type`` can be:

        - 'abc' to get an alphabet abc... and inverses ABC...

        - 'x0' to get an alphabet x0, x1,... and inverses X0, X1,...

        - 'a0' to get an alphabet a0, a1,... and inverses A0, A1,...

        EXAMPLES::

            sage: AlphabetWithInverses(['a','b','c'],['A','B','C'])
            Alphabet with inverses on ['a', 'b', 'c']

            sage: AlphabetWithInverses(4, type='abc')
            Alphabet with inverses on ['a', 'b', 'c', 'd']

            sage: AlphabetWithInverses(4, type='x0')
            Alphabet with inverses on ['x0', 'x1', 'x2', 'x3']

            sage: A = AlphabetWithInverses(['x1','x5'], type='x0')
            sage: A
            Alphabet with inverses on ['x1', 'x5']
            sage: A.add_new_letter()
            ('x0', 'X0')
            sage: A.add_new_letter()
            ('x2', 'X2')
            sage: A
            Alphabet with inverses on ['x0', 'x1', 'x2', 'x5']
        """
        if isinstance(alphabet,(int,Integer)):
            self._available = DynamicIntegerSet(alphabet)
        else:
            self._available = DynamicIntegerSet()
            for letter in alphabet:
                self._available.new(self._rank_letter(letter))

        from sage.categories.enumerated_sets import EnumeratedSets
        Parent.__init__(self, category=EnumeratedSets().Finite(), facade=(str,))

    def positive_letters(self):
        """
        The list of positive letters of this alphabet.

        EXAMPLES::

            sage: A = AlphabetWithInverses('abc')
            sage: A.positive_letters()
            ['a', 'b', 'c']
        """
        return [self._unrank_letter(i) for i in self._available]

    def negative_letters(self):
        """
        The list of negative letters

        EXAMPLES::

            sage: A = AlphabetWithInverses('abc')
            sage: A.negative_letters()
            ['A', 'B', 'C']
        """
        return [self._unrank_inverse_letter(i) for i in self._available]

    def __repr__(self):
        """
        String representation of self.
        """
        return "Alphabet with inverses on %s" %self.positive_letters()

    def __iter__(self):
        """
        Iterator through the letters of the alphabet.

        .. WARNING:

        The iterator is on all the letters of the alphabet (both
        positive and negative). This is NOT consistent with ```len()``.

        EXAMPLES::

            sage: A = AlphabetWithInverses(3, 'x0')
            sage: for letter in A: print letter
            x0
            x1
            x2
            X0
            X1
            X2
        """
        from itertools import chain
        return chain(self.positive_letters(), self.negative_letters())

    def cardinality(self):
        """
        The cardinality of the positive letters.

        This is equal to ``len()`.
        """
        return len(self._available)

    __len__ = cardinality

    def __contains__(self, letter):
        """
        Test whether the letter is contained in self

        TESTS::

            sage: A = AlphabetWithInverses(4)
            sage: all(letter in A for letter in A)
            True
            sage: 'b' in A
            True
            sage: 'B' in A
            True
            sage: 'e' in A
            False
            sage: 'a1' in A
            False
            sage: 142 in A
            False
            sage: A.remove_letter('b')
            sage: 'b' in A or 'B' in A
            False
            sage: all(letter in A for letter in A)
            True

            sage: A = AlphabetWithInverses(4, type='x0')
            sage: all(letter in A for letter in A)
            True
            sage: 'x2' in A
            True
            sage: 'x' in A
            False
            sage: 143 in A
            False
            sage: A.remove_letter('x3')
            sage: 'x3' in A or 'X3' in A
            False
            sage: all(letter in A for letter in A)
            True
        """
        return self.is_positive_letter(letter) or self.is_negative_letter(letter)

    def rank(self, letter):
        """
        Return the rank of the letter

        from 0 to card(self)-1: positive letters
        from card(self) to 2card(self)-1: negative letters
        """
        if self.is_positive_letter(letter):
            return self._rank_letter(letter)
        elif self.is_negative_letter(letter):
            return len(self) + self._rank_letter(letter)
        else:
            raise ValueError("{} not in the alphabet".format(letter))

    def __getitem__(self,n):
        """
        Return the letter with rank n.

        from 0 to card(self)-1: positive letters
        from card(self) to 2card(self)-1: negative letters
        """
        n = n.__index__()
        N = len(self)
        if n < 0:
            raise NotImplementedError("negative index not supported")
        if n > 2*N:
            raise IndexError("index out of range")
        if n < N:
            return self._unrank_letter(n)
        else:
            return self._unrank_inverse_letter(n-N)

    def inverse_letter(self, letter):
       """
       Inverse of ``letter``.
       """
       if self.is_positive_letter(letter):
           i = self._rank_letter(letter)
           return self._unrank_inverse_letter(i)
       elif self.is_negative_letter(letter):
           i = self._rank_letter(letter)
           return self._unrank_letter(i)
       else:
           raise ValueError("{} not in alphabet".format(letter))

    def to_positive_letter(self,letter):
        """
        Given letter a or a^-1 returns a.

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'],['A','B','C'])
            sage: A.to_positive_letter('b')
            'b'
            sage: A.to_positive_letter('B')
            'b'
        """
        return self._unrank_letter(self._rank_letter(letter))

    def are_inverse(self, a, b):
        """
        Test if the two letters are inverse of each other.
        """
        return self.inverse_letter(a) == b

    def less_letter(self,a,b):
        """
        ``True`` if ``a`` is before ``b`` in the alphabet.
        """
        return (self.rank(a)<=self.rank(b))

    def random_letter(self, exclude=None):
        """
        A random letter, different from the letters in ``exclude``.

        EXAMPLES::

            sage: A = AlphabetWithInverses('ehk')
            sage: A.random_letter()  # random
            'B'
        """
        if exclude is not None:
            letters = [a for a in self if a not in exclude]
        else:
            letters = list(self)

        if not letters:
            raise EmptySetError("no letter available")
        return choice(letters)

    def add_new_letter(self):
        """
        Adds a new letter to the alphabet.

        OUTPUT:

        The pair[positive_letter,negative_letter].
        """
        i = self._available.new()
        letter = self._unrank_letter(i)
        inverse = self._unrank_inverse_letter(i)
        return (letter,inverse)

    def add_new_letters(self,n=1):
        """
        Adds ``n`` new letters to the alphabet.

        OUTPUT:

        The list of [positive_letter,negative_letter] of new letters.
        """
        return [self.add_new_letter() for _ in range(n)]

    def remove_letter(self,a):
        """
        Remove the letter a (and its inverse) from the alphabet.

        EXAMPLES::

            sage: A=AlphabetWithInverses(4)
            sage: A.remove_letter('b')
            sage: print A
            Alphabet with inverses on ['a', 'c', 'd']
        """
        a = self.to_positive_letter(a)
        aa = self.inverse_letter(a)
        i = self._rank_letter(a)
        self._available.release(i)

class Alphabet_abc(AbstractAlphabetWithInverses):
    def _rank_letter(self, letter): return ord(letter.lower())-97
    def _unrank_letter(self, i): return chr(97+i)
    def _unrank_inverse_letter(self,i): return chr(65+i)

    def is_positive_letter(self, letter):
        """
        Test if the letter is a positive letter.

        EXAMPLES::

            sage: A = AlphabetWithInverses(3, 'abc')
            sage: A.is_positive_letter('a')
            True
            sage: A.is_positive_letter('d')
            False
            sage: A.is_positive_letter('A')
            False
        """
        return isinstance(letter,str) and \
               len(letter) == 1 and \
               ord(letter)-97 in self._available

    def is_negative_letter(self,letter):
        """
        Test if the letter is a negative letter.

        EXAMPLES::

            sage: A = AlphabetWithInverses(3, 'abc')
            sage: A.is_negative_letter('B')
            True
            sage: A.is_negative_letter('b')
            False
            sage: A.is_negative_letter('Z')
            False
        """
        return isinstance(letter, str) and \
               len(letter) == 1 and \
               ord(letter)-65 in self._available

    def copy(self):
        """
        A copy of self.
        """
        return Alphabet_abc(self.positive_letters(), self.negative_letters())

class Alphabet_prefix(AbstractAlphabetWithInverses):
    r"""
    EXAMPLES::

        sage: AlphabetWithInverses(5, type='x0')
        Alphabet with inverses on ['x0', 'x1', 'x2', 'x3', 'x4']
    """
    def __init__(self, prefix, prefix_inverse, alphabet, inverse):
        self._low = prefix
        self._upp = prefix_inverse
        AbstractAlphabetWithInverses.__init__(self, alphabet, inverse)

    def _rank_letter(self, letter): return int(letter[1:])
    def _unrank_letter(self, i): return self._low + str(i)
    def _unrank_inverse_letter(self,i): return self._upp + str(i)

    def is_positive_letter(self, letter):
        """
        Test if the letter is a positive letter.

        EXAMPLES::

            sage: A = AlphabetWithInverses(20, type='x0')
            sage: A.is_positive_letter('x12')
            True
            sage: A.is_positive_letter('x21')
            False
            sage: A.is_positive_letter('X0')
            False
        """
        if not isinstance(letter,str) or len(letter) < 2 or letter[0] != self._low:
            return False
        letter = letter[1:]
        return letter.isdigit() and int(letter) in self._available

    def is_negative_letter(self,letter):
        """
        Test if the letter is a negative letter.

        EXAMPLES::

            sage: A = AlphabetWithInverses(20, type='x0')
            sage: A.is_negative_letter('X12')
            True
            sage: A.is_negative_letter('X21')
            False
            sage: A.is_negative_letter('x0')
            False
        """
        if not isinstance(letter, str):
            return False

        if not isinstance(letter,str) or len(letter) < 2 or letter[0] != self._upp:
                return False
        letter = letter[1:]
        return letter.isdigit() and int(letter) in self._available

    def copy(self):
        r"""
        EXAMPLES::

            sage: A = AlphabetWithInverses(20, type='x0')
            sage: A.copy()
            Alphabet with inverses on ['x0', 'x1', 'x2', 'x3', 'x4', 'x5', 'x6',
            'x7', 'x8', 'x9', 'x10', 'x11', 'x12', 'x13', 'x14', 'x15', 'x16',
            'x17', 'x18', 'x19']
            sage: A.copy() is A
            False
        """
        return Alphabet_prefix(self._low, self._upp, self.positive_letters(), self.negative_letters())
