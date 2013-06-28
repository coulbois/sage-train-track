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
    
    def __str__(self):
        result=""
        for a in self: result+=a
        return result

    def __mul__(self,other):
        """
        Returns the reduced product of self and other assuming that self and other
        are reduced.

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
        return self.parent()(self[:len(self)-i]+other[i:])

    def inverse(self):
        """
        Returns the inverse of self. 
        """
        F=self.parent()
        A=F.alphabet()
        return F(A.inverse_letter(a) for a in reversed(self))
