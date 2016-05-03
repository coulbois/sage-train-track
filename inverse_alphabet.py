r"""
inverse_alphabet module, define Class for alphabet with inverse letters

AUTHORS:

- Thierry COULBOIS (2013-01-01): initial version
- Dominique BENIELLI (2016-02_15): AMU University
  <dominique.benielli@univ-amu.fr>, Integration in SageMath

EXAMPLES::

    sage: AlphabetWithInverses(['a','b','c'],['A','B','C'])
    Alphabet with inverses on ['a', 'b', 'c']
"""
#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from sage.structure.parent import Parent
from sage.rings.integer import Integer


class AlphabetWithInverses(Parent):
    """
    Class for alphabet with inverse letters.

    Intended to be used by FreeGroup.  Builds a finite ordered
    alphabet with an inverse for each letter. There must be no
    duplicate. Inverse letters are either given or assumed to be
    capitalized letters.

    EXAMPLES::

        sage: AlphabetWithInverses(['a','b','c'],['A','B','C'])
        Alphabet with inverses on ['a', 'b', 'c']

        sage: AlphabetWithInverses(['a','b','c'])
        Alphabet with inverses on ['a', 'b', 'c']

        sage: AlphabetWithInverses(3)
        Alphabet with inverses on ['a', 'b', 'c']

        sage: AlphabetWithInverses(3, type='x0')
        Alphabet with inverses on ['x0', 'x1', 'x2']

    AUTHORS:

    - Thierry Coulbois (2013-05-16)
    """

    def __init__(self, alphabet, inverse=None, type='abc'):
        """
        Builds a finite ordered alphabet with an inverse for each
        letter. There must be no duplicate. Inverse letters are either
        given or computed by capitalization.

        The alphabet can also be specified by the number of letters
        and its type (default is 'abc'). `

        INPUT:

        -``type`` can be:

            - 'abc' to get an alphabet abc... and inverses ABC...

            - 'x0' to get an alphabet x0, x1,... and inverses X0, X1,...

            - 'a0' to get an alphabet a0, a1,... and inverses A0, A1,...

        EXAMPLES::

            sage: AlphabetWithInverses(['a','b','c'],['A','B','C'])
            Alphabet with inverses on ['a', 'b', 'c']

            sage: AlphabetWithInverses(4, type='abc')
            Alphabet with inverses on ['a', 'b', 'c', 'd']

            sage: AlphabetWithInverses(4, type='a0')
            Alphabet with inverses on ['a0', 'a1', 'a2', 'a3']

            sage: AlphabetWithInverses(4, type='x0')
            Alphabet with inverses on ['x0', 'x1', 'x2', 'x3']

        TESTS::

            sage: A = AlphabetWithInverses(['a', 'b'])
            sage: B = loads(dumps(A))
            sage: A._positive == B._positive
            True
            sage: A._negative == B._negative
            True
            sage: A._type == B._type
            True
        """
        if isinstance(alphabet, (int, Integer)):
            if type == 'abc':
                if alphabet < 27:
                    self._positive = \
                        ["%c" % (i + 97) for i in xrange(alphabet)]
                    self._negative = \
                        ["%c" % (i + 65) for i in xrange(alphabet)]
                else:
                    self._positive =\
                        ["%c" % (i + 97) for i in xrange(26)] + \
                        ["x%s" % i for i in xrange(alphabet - 26)]
                    self._negative = \
                        ["%c" % (i + 65) for i in xrange(26)] + \
                        ["X%s" % i for i in xrange(alphabet - 26)]

            elif type == 'a0':
                self._positive = ["a%s" % i for i in xrange(alphabet)]
                self._negative = ["A%s" % i for i in xrange(alphabet)]
            elif type == 'num' and alphabet < 10:
                self._positive = ["%s" % i for i in xrange(alphabet)]
                self._negative = ["%s" % i for i in xrange(alphabet)]
            else:  # type is assumed to be 'x0'
                self._positive = ["x%s" % i for i in xrange(alphabet)]
                self._negative = ["X%s" % i for i in xrange(alphabet)]

        else:
            self._positive = list(alphabet)
            if inverse is not None:
                self._negative = list(inverse)
            else:
                self._negative = [a.upper() for a in self._positive]

        self._inverse = {}
        self._inverse.update(
            (self._negative[i], self._positive[i])
            for i in xrange(len(self._positive)))
        self._inverse.update(
            (self._positive[i], self._negative[i])
            for i in xrange(len(self._negative)))
        self._type = type

    def __repr__(self):
        """
        This would be hidden without the ``.. automethod::``

        String representation of self.

        OUTPUT:

        - return a string reprensentation of 'self'

        TESTS::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'])
            sage: A.__repr__()
            "Alphabet with inverses on ['a', 'b', 'c']"
        """
        return "Alphabet with inverses on %s" % str(self._positive)

    def __iter__(self):
        """
        This would be hidden without the ``.. automethod::``

        Iterator through the letters of the alphabet.

        OUTPUT:

        - return a iterator on 'self'

        TEST::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'])
            sage: A.__iter__().next()
            'a'

        WARNING:

        The iterator is on all the letters of the alphabet (both
        positive and negative). This is NOT consistent with ```len()``.
        """
        A = AlphabetWithInverses(['a','b','c'], ['A','B','C'])

        return iter(self._positive + self._negative)
        #return iter(self._positive)

    def copy(self):
        """
        A copy of self.

        OUTPUT:

        - return a copy of 'self'

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'],type='abc')
            sage: A.copy()
            Alphabet with inverses on ['a', 'b', 'c']
        """
        return AlphabetWithInverses(self.positive_letters()[:],
                                    self.negative_letters()[:], self._type)

    def cardinality(self):
        """
        The cardinality of the positive letters.

        OUTPUT:

        - return number of cardinality of 'self'

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'],type='abc')
            sage: A.cardinality()
            3

        WARNING:

        This is equal to ``len()``.
        """
        return len(self._positive)

    def __contains__(self, letter):
        """
        This would be hidden without the ``.. automethod::``

        Test whether the letter is contained in self

        INPUT:

        - ``letter`` -- letter to test

        OUTPUT:

        - return True if the input 'letter'it is present in positive
        or negatve alphabet , False if not

        TESTS::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'],type='abc')
            sage: A.__contains__('a')
            True
            sage: A.__contains__('B')
            True
            sage: A.__contains__('d')
            False
        """
        return letter in self._positive or letter in self._negative

    def __len__(self):
        '''
        This would be hidden without the ``.. automethod::``

        OUTPUT:

        - return len of 'self'

        TESTS::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'],type='abc')
            sage: A.__len__()
            3
        '''
        return len(self._positive)

    def rank(self, letter):
        """
        Return the rank of the letter
        from 0 to card(self)-1: positive letters
        from card(self) to 2card(self)-1: negative letters

        INPUT:

        - ``letter`` -- letter to test

        OUTPUT:

        - return rank of the input letter in self

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'],type='abc')
            sage: A.rank('b')
            1
            sage: A.rank('B')
            4
            sage: A.rank('d')
            False
        """
        if letter in self._positive:
            return self._positive.index(letter)
        elif letter in self._negative:
            return self.cardinality() + self._negative.index(letter)
        else:
            return False

    def __getitem__(self, n):
        """
        This would be hidden without the ``.. automethod::``

        Return the letter with rank n.

        from 0 to card(self)-1: positive letters
        from card(self) to 2card(self)-1: negative letters

        INPUT:

        - ``n`` -- the number of index

        OUTPUT:

        - return rank of the input letter in self

        TESTS::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'], type='abc')
            sage: A.unrank(2)
            'c'
            sage: A.unrank(4)
            'B'
            sage: A.unrank(7)
            False
        """
        if n < self.cardinality():
            return self._positive[n]
        elif  n < 2 * self.cardinality():
            return self._negative[n - self.cardinality()]
        else:
            return False

    def unrank(self, n):
        """
        .. automethod:: __getitem__
        """
        return  self.__getitem__(n)
        
    def inverse_letter(self, letter):
        """
        Inverse of ``letter``.

        INPUT:

        - ``letter`` -- letter to inverse

        OUTPUT:

        - return the inverse of the input letter

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'],type='abc')
            sage: A.inverse_letter('b')
            'B'
            sage: A.inverse_letter('B')
            'b'
        """
        return self._inverse[letter]

    def are_inverse(self, a, b):
        """
        Test if the two letters are inverse of each other.

        INPUT:

        - ``a`` -- letter to compare with ''b''
        - ''b`` -- letter to compare with ''a''

        OUTPUT:

        - return True if ''a'' is inverse of ''b''

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'],type='abc')
            sage: A.are_inverse('a','A')
            True
            sage: A.are_inverse('b','A')
            False
        """
        return self._inverse[a] == b

    def is_positive_letter(self, letter):
        """
        Test if the letter is a positive letter.
                INPUT:

        - ``letter`` -- letter to test

        OUTPUT:

        - return True if ''letter'' is positive  and False if Not

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'],type='abc')
            sage: A.is_positive_letter('a')
            True
            sage: A.is_positive_letter('A')
            False
        """
        return letter in self._positive

    def is_negative_letter(self, letter):
        """
        Test if the letter is a negative letter.

        INPUT:

        - ``letter`` -- letter to test

        OUTPUT:

        - return True if ''letter'' is negative  and False if Not

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'],type='abc')
            sage: A.is_negative_letter('a')
            False
            sage: A.is_negative_letter('A')
            True
        """
        return letter in self._negative

    def to_positive_letter(self, letter):
        """
        Given letter a or a^-1 returns a.

        INPUT:

        - ``letter`` -- letter to test

        OUTPUT:

        - return True if ''letter'' is negative  and False if Not

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'],['A','B','C'])
            sage: A.to_positive_letter('b')
            'b'
            sage: A.to_positive_letter('B')
            'b'
        """
        if letter in self._positive:
            return letter
        elif letter in self._negative:
            return self._inverse[letter]
        else:
            raise ValueError("The letter %s is not in the alphabet %s"
                             % (str(letter), str(self)))

    def positive_letters(self):
        """
        The list of positive letters of this alphabet.

        OUTPUT:

        - the list of the positive letters of this alphabet

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'],['A','B','C'])
            sage: A.positive_letters()
            ['a', 'b', 'c']
        """
        return self._positive

    def negative_letters(self):
        """
        The list of negative letters

        OUTPUT:

        - the list of the negative letters of this alphabet

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'],['A','B','C'])
            sage: A.negative_letters()
            ['A', 'B', 'C']
        """
        return self._negative

    def compare_letters(self, a, b):
        """
        Compares the letters ``a`` and ``b`` according to their
        rank in ``self``.

        INPUT:

        - ``a`` -- letter to compare with ''b''
        - ``b`` -- letter to compare with ''a''

        OUTPUT:

        - return        -1 if a < b
                         0 if a == b
                         1 if a > b

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'])
            sage: A.compare_letters('a','A')
            -1
            sage: A.compare_letters('c','a')
            1
            sage: A.compare_letters('B','B')
            0
        """
        return cmp(self.rank(a), self.rank(b))

    def less_letter(self, a, b):
        """
        ``True`` if ``a`` is before ``b`` in the alphabet.

        INPUT:

        - ``a`` -- letter to compare with ''b''
        - ``b`` -- letter to compare with ''a''

        OUTPUT:

        - return True if  ``a`` is before ``b`` in the alphabet, False if Not

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'])
            sage: A.less_letter('a','A')
            True
            sage: A.less_letter('c','a')
            False
        """
        return (self.rank(a) <= self.rank(b))

    def random_letter(self, exclude=[]):
        """
        A random letter, different from the letters in ``exclude``.

        INPUT:

        - ``exclude`` -- (default:[]) list of letter to exclude

        OUTPUT:

        - return a random letter different from letter in exclude

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'])
            sage: A.random_letter(['a','b','c','A','C'])
            'B'
        """
        from sage.misc.prandom import randint

        done = False
        while not done:
            j = randint(0, 2 * len(self) - 1)
            a = self[j]
            done = a not in exclude
        return a

    def _new_letter(self):
        """
        This would be hidden without the ``.. automethod::``

        A pair [positive_letter, negative_letter] not already in the
        alphabet.

        The new_letter is constructed from the type of the
        alphabet. If the type is 'abc' and all 26 ASCII letters are
        used, looks for ['a0','A0'] etc.

        OUTPUT:

        - return a new pair of [positive_letter, negative_letter] followed the
          alphabet

        TESTS::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'])
            sage: A._new_letter()
            ['d', 'D']
            sage: A = AlphabetWithInverses(4, type='a0')
            sage: A._new_letter()
            ['a4', 'A4']
            sage: A = AlphabetWithInverses(3, type='x0')
            sage: A._new_letter()
            ['x3', 'X3']
        """
        i = 0
        done = False

        if self._type == 'abc':
            while i < 26 and not done:
                e = "%c" % (i + 97)
                if e not in self.positive_letters():
                    done = True
                    result = [e, "%c" % (i + 65)]
                i += 1
        elif self._type == 'x0':
            i = 0
            done = False
            while not done:
                e = "x%s" % i
                if e not in self.positive_letters():
                    done = True
                    result = [e, "X%i" % i]
                i += 1
        i = 0
        while not done:
            e = "a%s" % i
            if e not in self.positive_letters():
                done = True
                result = [e, "A%i" % i]
            i += 1

        return result

    def _new_letters(self, n=1):
        """
        This would be hidden without the ``.. automethod::``

        A list of length ``n`` of pairs [positve_letter, negative_letter]
        not already in the alphabet.

        The new_letters are constructed from the type of the
        alphabet. If the type is 'abc' and all 26 ASCII letters are
        used, looks for ['a0','A0'] etc.

        INPUT:

        - ``n`` -- (default: 1) the number of pairs of
          [positve_letter, negative_letter]

        OUTPUT:

        - return a list of new pair of [positive_letter, negative_letter]
          followed the alphabet


        TESTS::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'])
            sage: A._new_letters(n=3)
            [['d', 'D'], ['e', 'E'], ['f', 'F']]
            sage: A = AlphabetWithInverses(4, type='a0')
            sage: A._new_letters(n=2)
            [['a4', 'A4'], ['a5', 'A5']]
            sage: A = AlphabetWithInverses(3, type='x0')
            sage: A._new_letters(n=1)
            [['x3', 'X3']]
        """
        i = 0
        result = []

        if self._type == 'abc':
            while i < 26 and n > 0:
                e = "%c" % (i + 97)
                if e not in self.positive_letters():
                    n = n - 1
                    result.append([e, "%c" % (i + 65)])
                i += 1

        elif self._type == 'x0':
            while n > 0:
                e = "x%s" % i
                if e not in self.positive_letters():
                    result.append([e, "X%s" % i])
                    n = n - 1
                i += 1
        i = 0
        while n > 0:
            e = "a%s" % i
            if e not in self.positive_letters():
                result.append([e, "A%s" % i])
                n = n - 1
            i += 1

        return result

    def add_new_letter(self):
        """
        Adds a new letter to the alphabet.
        The pair[positive_letter,negative_letter].

        OUTPUT:

        - return a new pair of [positive_letter, negative_letter] followed the
          alphabet

        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'])
            sage: A.add_new_letter()
            ['d', 'D']
            sage: A = AlphabetWithInverses(4, type='a0')
            sage: A.add_new_letter()
            ['a4', 'A4']
            sage: A = AlphabetWithInverses(3, type='x0')
            sage: A.add_new_letter()
            ['x3', 'X3']

        .. automethod:: _new_letter

        """
        new_letter = self._new_letter()
        self._positive.append(new_letter[0])
        self._negative.append(new_letter[1])
        self._inverse[new_letter[0]] = new_letter[1]
        self._inverse[new_letter[1]] = new_letter[0]
        return new_letter

    def add_new_letters(self, n=1):
        """
        Adds ``n`` new letters to the alphabet.

        INPUT:

        - ``n`` -- (default: 1) the number of pairs of
          [positve_letter, negative_letter]


        OUTPUT:

        - return the list of [positive_letter,negative_letter] of new letters.


        EXAMPLES::

            sage: A = AlphabetWithInverses(['a','b','c'], ['A','B','C'])
            sage: A.add_new_letters(3)
            [['d', 'D'], ['e', 'E'], ['f', 'F']]
            sage: A = AlphabetWithInverses(4, type='a0')
            sage: A.add_new_letters(2)
            [['a4', 'A4'], ['a5', 'A5']]
            sage: A = AlphabetWithInverses(3, type='x0')
            sage: A.add_new_letters(1)
            [['x3', 'X3']]

        .. automethod:: _new_letters
        """
        new_letters = self._new_letters(n)
        self._positive += [a[0] for a in new_letters]
        self._negative += [a[1] for a in new_letters]
        self._inverse.update((a[0], a[1]) for a in new_letters)
        self._inverse.update((a[1], a[0]) for a in new_letters)
        return new_letters

    def remove_letter(self, a):
        """
        Remove the letter a (and its inverse) from the alphabet.

        INPUT:

        - ``a`` -- letter to remove

        EXAMPLES::

            sage: A = AlphabetWithInverses(4)
            sage: A.remove_letter('b')
            sage: print A
            Alphabet with inverses on ['a', 'c', 'd']
        """
        aa = self.to_positive_letter(a)
        aaa = self.inverse_letter(aa)
        self._positive.remove(aa)
        self._negative.remove(aaa)
        self._inverse.pop(aa)
        self._inverse.pop(aaa)
