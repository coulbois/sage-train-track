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
        FreeGroupWord: 'aba'

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

    def __invert__(self):
        """
        Inverse of self.

        EXAMPLES::

            sage: F = FreeGroup('abc')
            sage: ~F('abCbA')
            word: aBcBA
            sage: F('abCbA').inverse()
            word: aBcBA
        """
        F=self.parent()
        A=F.alphabet()
        return F(A.inverse_letter(a) for a in reversed(self))

    inverse = __invert__
