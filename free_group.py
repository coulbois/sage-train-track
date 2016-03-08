# coding=utf-8
r"""
Combinatorial classes of words.

To define a new class of words, please refer to the documentation file:
sage/combinat/words/notes/word_inheritance_howto.txt

AUTHORS:
   Thierry Coulbois <thierry.coulbois@univ-amu.fr>
"""

# *****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# *****************************************************************************

try:
    # after trac ticket #19619
    from sage.combinat.words.words import FiniteWords
except ImportError:
    # before trac ticket #19619
    from sage.combinat.words.words import FiniteWords_over_OrderedAlphabet \
        as FiniteWords

from inverse_alphabet import AlphabetWithInverses
from free_group_word import FreeGroupWord


class FreeGroup(FiniteWords):
    """
    Free group of finite rank.

    EXAMPLES::

    sage: A = AlphabetWithInverses(['a','b'])
    sage: FreeGroup(A)
    Free group over ['a', 'b']

    sage: FreeGroup(3)
    Free group over ['a', 'b', 'c']

    sage: A = AlphabetWithInverses(2,type='x0')
    sage: FreeGroup(A)
    Free group over ['x0', 'x1']

    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version
    """

    def __init__(self, alphabet):
        if not isinstance(alphabet, AlphabetWithInverses):
            alphabet = AlphabetWithInverses(alphabet)
        FiniteWords.__init__(self, alphabet)
        self.element_class = FreeGroupWord

    def __repr__(self):
        """
        String representation for free group
        """
        return "Free group over %s" % str(self._alphabet.positive_letters())

    def __call__(self, data=None, length=None, datatype=None, caching=True,
                 **kwds):
        r"""
        Build an element of this free group from data.

        WARNING:

        No reduction is performed.


        SEE ALSO:

        FreeGroupWord.reduce()
        """
        if data == None:
            data=[]
        return FreeGroupWord(self, data)
