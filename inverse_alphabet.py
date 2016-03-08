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

        sage: AlphabetWithInverse(['a','b','c'],['A','B','C'])
        Alphabet with inverse on ['a', 'b', 'c']

        sage: AlphabetWithInverse(['a','b','c'])
        Alphabet with inverse on ['a', 'b', 'c']

        sage: AlphabetWithInverse(3)
        Alphabet with inverse on ['a', 'b', 'c']

        sage: AlphabetWithInverses(3,type='x0')
        Alphabet with inverse on ['x0', 'x1', 'x2']

    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version

    """

    def __init__(self,alphabet,inverse=None,type='abc'):
        """
        Builds a finite ordered alphabet with an inverse for each
        letter. There must be no duplicate. Inverse letters are either
        given or computed by capitalization.

        The alphabet can also be specified by the number of letters
        and its type (default is 'abc'). `

        INPUT:

        `type`` can be:

        - 'abc' to get an alphabet abc... and inverses ABC...

        - 'x0' to get an alphabet x0, x1,... and inverses X0, X1,...

        - 'a0' to get an alphabet a0, a1,... and inverses A0, A1,...

        EXAMPLES::

        sage: AlphabetWithInverses(['a','b','c'],['A','B','C'])
        Alphabet with inverses on ['a', 'b', 'c']

        sage: AlphabetWithInverses(4,'abc')
        Alphabet with inverses on ['a', 'b', 'c', 'd']

        sage: AlphabetWithInverses(4,'x0')
        Alphabet with inverses on ['x0', 'x1', 'x2', 'x3']


        TESTS::

        sage: A = AlphabetWithInverses(['a','b'])
        sage: A == loads(dumps(A))
        True

        """
        if isinstance(alphabet,(int,Integer)):
            if type=='abc':
                if alphabet<27:
                    self._positive=["%c" % (i+97) for i in xrange(alphabet)]
                    self._negative=["%c" % (i+65) for i in xrange(alphabet)]
                else:
                    self._positive=["%c" % (i+97) for i in xrange(26)]+["x%s" % i for i in xrange(alphabet-26)]
                    self._negative=["%c" % (i+65) for i in xrange(26)]+["X%s" % i for i in xrange(alphabet-26)]

            elif type=='a0':
                self._positive=["a%s" % i for i in xrange(alphabet)]
                self._negative=["A%s" % i for i in xrange(alphabet)]
            elif type=='num' and alphabet<10:
                self._positive=["%s" % i for i in xrange(alphabet)]
                self._negative=["%s" % i for i in xrange(alphabet)]
            else: #type is assumed to be 'x0'
                self._positive=["x%s" % i for i in xrange(alphabet)]
                self._negative=["X%s" % i for i in xrange(alphabet)]


        else:
            self._positive = list(alphabet)
            if inverse is not None:
                self._negative = list(inverse)
            else:
                self._negative = [a.upper() for a in self._positive]

        self._inverse = {}
        self._inverse.update((self._negative[i],self._positive[i]) for i in xrange(len(self._positive)))
        self._inverse.update((self._positive[i],self._negative[i]) for i in xrange(len(self._negative)))
        self._type=type

    def __repr__(self):
        """
        String representation of self.
        """
        return "Alphabet with inverses on %s" %str(self._positive)

    def __iter__(self):
        """
        Iterator through the letters of the alphabet.

        WARNING:

        The iterator is on all the letters of the alphabet (both
        positive and negative). This is NOT consistent with ```len()``.
        """
        return iter(self._positive + self._negative)
        #return iter(self._positive)

    def copy(self):
        """
        A copy of self.
        """
        return AlphabetWithInverses(self.positive_letters()[:],self.negative_letters()[:],self._type)



    def cardinality(self):
        """
        The cardinality of the positive letters.

        WARNING:

        This is equal to ``len()``.
        """
        return len(self._positive)

    def __contains__(self,letter):
        """
        Test whether the letter is contained in ``self``.
        """
        return letter in self._positive or letter in self._negative

    def __len__(self):
        """
        Number of positive letters in ``self``.
        """
        return len(self._positive)

    def rank(self,letter):
        """
        Return the rank of the ``letter``.

        from 0 to card(self)-1: positive letters
        from card(self) to 2card(self)-1: negative letters
        """
        if letter in self._positive:
            return self._positive.index(letter)
        else:
            return self.cardinality()+self._negative.index(letter)

    def __getitem__(self,n):
        """
        Return the letter with rank ``n``.

        from 0 to card(self)-1: positive letters
        from card(self) to 2card(self)-1: negative letters
        """
        if n < self.cardinality():
            return self._positive[n]
        else:
            return self._negative[n-self.cardinality()]


    unrank=__getitem__
        
    def inverse_letter(self,letter):
       """
       Inverse of ``letter``.
       """
       return self._inverse[letter]

    def are_inverse(self,a,b):
        """
        ``True`` if the two letters are inverse of each other.
        """
        return self._inverse[a] == b

    def is_positive_letter(self,letter):
        """
        ``True`` if ``letter`` is a positive letter.
        """
        return letter in self._positive

    def is_negative_letter(self,letter):
        """
        ``True`` if ``letter`` is a negative letter.
        """
        return letter in self._negative

    def to_positive_letter(self,letter):
        """
        The positive letter in the pair ``(letter,A.inverse_letter(letter))``.

        EXAMPLES::

            sage: A = AlphabetWithInverse(['a','b','c'],['A','B','C'])
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
           raise ValueError, "The letter %s is not in the alphabet %s" %(str(letter),str(self))

    def positive_letters(self):
        """
        List of positive letters of ``self``.
        """
        return self._positive

    def negative_letters(self):
        """
        List of negative letters of ``self``.
        """
        return self._negative

    def less_letter(self,a,b):
        """
        ``True`` if ``a`` is before ``b`` in ``self``.

        The order is computed according to the rank of letters. In
        particular positive letters are smaller than negative letters.
        """

        return (self.rank(a)<=self.rank(b))

    def compare_letters(self,a,b):
        """
        Compares the letters ``a`` and ``b`` according to their rank in ``self``.

        OUTPUT:
        
        -1 if a<b
        0 if a==b
        1 if a>b
        """
        return cmp(self.rank(a),self.rank(b))

    def random_letter(self,exclude=[]):
        """
        A random letter, different from the letters in ``exclude``.
        """
        from sage.misc.prandom import randint

        done=False
        while not done:
            j=randint(0,2*len(self)-1)
            a=self[j]
            done=a not in exclude
        return a

    def _new_letter(self):
        """
        A pair [positive_letter, negative_letter] not already in the
        alphabet.

        The new letter is constructed from the type of ``self``. If
        the type is 'abc' and all 26 ASCII letters are used, looks for
        ['a0','A0'] etc.

        """

        i=0 done=False

        if self._type=='abc':
            while i<26 and not done:
                e="%c"%(i+97)
                if e not in self.positive_letters():
                    done=True
                    result=[e,"%c"%(i+65)]
                i+=1
        elif self._type=='x0':
            i=0
            done=False
            while not done:
                e="x%s"%i
                if e not in self.positive_letters():
                    done=True
                    result=[e,"X%i"%i]
                i+=1
        i=0
        while not done:
            e="a%s"%i
            if e not in self.positive_letters():
                done=True
                result=[e,"A%i"%i]
            i+=1


        return result

    def _new_letters(self,n=1):
        """
        A list of length ``n`` of pairs [positve_letter, negative_letter]
        not already in the alphabet.

        The new_letters are constructed from the type of the
        alphabet. If the type is 'abc' and all 26 ASCII letters are
        used, looks for ['a0','A0'] etc.
        """
        i=0
        result=[]

        if self._type=='abc':
            while i<26 and n>0:
                e="%c"%(i+97)
                if e not in self.positive_letters():
                    n=n-1
                    result.append([e,"%c"%(i+65)])
                i+=1

        elif self._type=='x0':
            while n>0:
                e="x%s"%i
                if e not in self.positive_letters():
                    result.append([e,"X%s"%i])
                    n=n-1
                i+=1
        i=0
        while n>0:
            e="a%s"%i
            if e not in self.positive_letters():
                result.append([e,"A%s"%i])
                n=n-1
            i+=1


        return result

    def add_new_letter(self):
        """
        Adds a new letter to the alphabet.

        The new letter is constructed from the type of ``self``. If
        the type is ``'abc'`` and all 26 ASCII letters are used, looks
        for ['a0','A0'] etc.

        OUTPUT:

        The pair[positive_letter,negative_letter].

        SEE ALSO:

        AlphabetWihInverses._new_letter()
        """
        new_letter=self._new_letter()
        self._positive.append(new_letter[0])
        self._negative.append(new_letter[1])
        self._inverse[new_letter[0]]=new_letter[1]
        self._inverse[new_letter[1]]=new_letter[0]
        return new_letter


    def add_new_letters(self,n=1):
        """
        Adds ``n`` new letters to the alphabet.

        The new letters are constructed from the type ``self``. If the
        type is 'abc' and all 26 ASCII letters are used, looks for
        ``['a0','A0']`` etc.


        OUTPUT:

        The list of [positive_letter,negative_letter] of new letters.
        """
        new_letters=self._new_letters(n)
        self._positive+=[a[0] for a in new_letters]
        self._negative+=[a[1] for a in new_letters]
        self._inverse.update((a[0],a[1]) for a in new_letters)
        self._inverse.update((a[1],a[0]) for a in new_letters)
        return new_letters

    def remove_letter(self,a):
        """
        Remove the letter ``a`` (and its inverse) from ``self``.

        EXAMPLES::

            sage: A=AlphabetWithInverses(4)
            sage: A.remove_letter('b')
            sage: print A
            Alphabet with inverses on ['a','c','d']

        """
        aa=self.to_positive_letter(a)
        aaa=self.inverse_letter(aa)
        self._positive.remove(aa)
        self._negative.remove(aaa)
        self._inverse.pop(aa)
        self._inverse.pop(aaa)

