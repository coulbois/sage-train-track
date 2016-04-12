# coding=utf-8
r"""
Combinatorial classes of words.

To define a new class of words, please refer to the documentation file:
sage/combinat/words/notes/word_inheritance_howto.txt

AUTHORS:

- Thierry COULBOIS (2013-01-01): initial version

- Dominique BENIELLI (2016-02_15):
AMU University <dominique.benielli@univ-amu.fr>, Integration in SageMath

EXAMPLES::

sage: A = AlphabetWithInverses(['a','b'])
sage: FreeGroup(A)
Free group over ['a', 'b']
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
    Free group of finite rank .

    EXAMPLES::

    sage: A = AlphabetWithInverses(['a','b'])
    sage: FreeGroup(A)
    Free group over ['a', 'b']

    sage: FreeGroup(3)
    Free group over ['a', 'b', 'c']

    sage: A = AlphabetWithInverses(2, type='x0')
    sage: FreeGroup(A)
    Free group over ['x0', 'x1']

    sage: A = AlphabetWithInverses(2, type='a0')
    sage: FreeGroup(A)
    Free group over ['a0', 'a1']

    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version
    """

    def __init__(self, alphabet):
        '''
        This would be hidden without the ``.. automethod::``

        INPUT:

        - ``alphabet`` -- alphabet or number for len of Alphabet to construct

        OUTPUT: instance of FreeGoupWord

        '''

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
        This would be hidden without the ``.. automethod::``

        Build an element of this free group from data.

        INPUT:

        - ``data`` -- (default: None) to  construct alphabet
        -``length``  -- (default: None)
        -``datatype``
        -``caching`` -- (default: True)

        OUTPUT: instance of FreeGroupWord

        WARNING:

        No reduction is performed.


        SEE ALSO:

        FreeGroupWord.reduce()
        """
        if data == None:
            data=[]
        return FreeGroupWord(self, data)
