#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.combinat.words.word import FiniteWord_list


class FreeGroupWord(FiniteWord_list):
    """
    Elements of a free group of finite rank.

    EXAMPLES::

        sage: F=FreeGroup(3)
        sage: w=F('aba')
        word: 'aba'

    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version
    """
    def __hash__(self):
        r"""
        TESTS:

        Haaaaaaaaaaaaaaaa.... I hate words in Sage::

            sage: W = Words('abcABC')
            sage: hash(W('aCA'))
            193377032
            sage: hash(W('Aca'))
            193377032
        """
        return hash(tuple(self))

    def __str__(self):
        result=""
        for a in self: result+=a
        return result

    def __mul__(self,other):
        """
        Reduced product of ``self`` and ``other``.

        WARNING:

        ``self`` and ``other``are assumed to be reduced.

        EXAMPLES::

        sage: F=FreeGroup(3)
        sage: u=F('abAc')
        sage: v=F('Caa')
        sage: u*v
          word: aba

        """
        A=self.parent().alphabet()
        i=0
        while (i<len(self) and i<len(other) and A.are_inverse(self[-i-1],other[i])):
            i=i+1
        return self.parent()(list(self[:len(self)-i])+list(other[i:]))

    def __pow__(self,exp):
        """
        Reduced power of ``self`` to ``exp``.

        ``exp`` can be any integer (positive or negative).

        EXAMPLES::

        sage: F=FreeGroup(3)
        sage: w=F('ababA')
        sage: w**3
           word: ababbabbabA
        sage: w**-2
           word: aBABBABA
        """
        F=self.parent()
        if exp==0 or len(self)==0:
            return F()

        A=F.alphabet()
        i=0
        done=False
        l=len(self)
        while self[i]==A.inverse_letter(self[l-i-1]): i+=1
        w=self
        c=l-i-i #cyclically reduced length of self
        ii=i
        if exp<0:
            w=self[i:l-i].inverse()
            exp=-exp
            ii=0
        max=c*exp+i
        fcn=lambda j: self[j] if j<i else (w[ii+((j-i)%c)] if j<max else self[j-max+c+i])
        return F(fcn(j) for j in xrange(max+i))
            
        
            

    def __invert__(self):
        """
        Inverse of self.

        EXAMPLES::

            sage: F = FreeGroup('abc')
            sage: F('abCbA')
            word: aBcBA
            sage: F('abCbA').inverse()
            word: aBcBA
        """
        F=self.parent()
        A=F.alphabet()
        return F(A.inverse_letter(a) for a in reversed(self))

    inverse = __invert__
