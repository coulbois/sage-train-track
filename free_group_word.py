# coding=utf-8
r"""
free_group_word.py module, define class for FreeGroupWord

Combinatorial classes of words.

AUTHORS:

- Thierry COULBOIS (2013-01-01): initial version

- Dominique BENIELLI (2016-02_15):
AMU University <dominique.benielli@univ-amu.fr>, Integration in SageMath

EXAMPLES::

sage: A =  AlphabetWithInverses(['a','b'])
sage: fw = FiniteWords(A)
sage: FreeGroupWord(fw,['a','b','c','d'])
word: abcd
"""
# *****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# *****************************************************************************
# - modified by Dominique 03/03/20016 :  major changes pep8 correction
from sage.combinat.words.word import FiniteWord_list
from sage.combinat.words.word import Word_class


class FreeGroupWord(FiniteWord_list):
    """
    Elements of a FreeGroupWord  word of finite rank.

    EXAMPLES::

        sage: A =  AlphabetWithInverses(6)
        sage: fw = FiniteWords(A)
        sage: FreeGroupWord(fw,['a','b','c','d'])
        word: abcd

    AUTHORS:

    - Thierry Coulbois (2013-05-16):
    - Dominique Benielli (2016-03-09)

    """

    def __hash__(self):
        """
        This would be hidden without the ``.. automethod::``

        OUTPUT:

        - return hash number of words
        """
        return hash(tuple(self))

    def __str__(self):
        """
        This would be hidden without the ``.. automethod::``

        OUTPUT:

        - return the string represention of FreeGroupWord



        EXAMPLES::

        sage: A =  AlphabetWithInverses(6)
        sage: fw = FiniteWords(A)
        sage: FGW = FreeGroupWord(fw,['a','b','c','d'])
        sage: FGW.__str__()
        'abcd'
        """

        result = ""
        for a in self:
            result += a
        return result

    def __mul__(self, other):
        """
        This would be hidden without the ``.. automethod::``

        Reduced product of ``self`` and ``other``.

        Cancellation is performed between the end of ``self`` and the
        beginning of ``other``. But not inside ``self`` and ``other``
        if they were not reduced.

        INPUT:

        - ``other`` -- a other FreeGroupWord for operation with ``self''

        OUTPUT:

        - return the reduced product of  ``self`` and ``other``

        WARNING:

        ``self`` and ``other``are assumed to be reduced.

        EXAMPLES::

        sage: A =  AlphabetWithInverses(3)
        sage: fw = FiniteWords(A)
        sage: FGW = FreeGroupWord(fw,['a','b','c'])
        sage: u = FGW('abAc')
        sage: v = F('Caa')
        sage: u * v
        word: aba

        """
        A = self.parent().alphabet()
        i = 0
        while (i < len(self) and i < len(other) and A.are_inverse(self[-i - 1],
                                                                  other[i])):
            i = i + 1
        return self.parent()(list(self[:len(self) - i]) + list(other[i:]))

    def __pow__(self, exp):
        """
        Reduced power of ``self`` to ``exp``.

        INPUT:

        - ``exp`` -- value of the exponent

        OUTPUT:

        - return  the power ``exp'' of ``self`` list

        ``exp`` can be any integer (positive or negative).

        EXAMPLES::

        sage: F=FreeGroupWord(3)
        sage: w=F('ababA')
        sage: w**3
           word: ababbabbabA
        sage: w**-2
           word: aBABBABA
        """
        F = self.parent()
        if exp == 0 or len(self) == 0:
            return F()

        A = F.alphabet()
        i = 0
        done = False
        l = len(self)
        while self[i] == A.inverse_letter(self[l - i - 1]):
            i += 1
        w = self
        c = l - i - i  # cyclically reduced length of self
        ii = i
        if exp < 0:
            w = self[i:l - i].inverse()
            exp = -exp
            ii = 0
        max = c * exp + i

        def fcn(j):
            return self[j] if j < i else (
                w[ii + ((j - i) % c)] if j < max else self[j - max + c + i])

        # fcn = lambda j: self[j] if j < i else (
        # w[ii + ((j - i) % c)] if j < max else self[j - max + c + i])
        return F(fcn(j) for j in xrange(max + i))

    def __cmp__(self, other):
        """
        Comparison of ``self`` and ``other`` in alphabetical order.

        WARNING:

        No reduction is performed, thus ``self`` and ``other`` are
        assumed to be reduced.

        EXAMPLES::

        sage: F=FreeGroup(3)
        sage: F("aba")<F("abbb")
        True
        sage: F("aba")==F("aba")
        True

        """
        if not isinstance(other, Word_class):
            return NotImplemented
        result = False
        k = 0
        while(k < len(self) and k < len(other) and self[k] == other[k]):
            k = k + 1
        if (k == len(self) and k == len(other)):
            result = 0
        elif (k == len(self)):
            result = -1
        elif (k == len(other)):
            result = 1
        else:
            result = self.parent().alphabet().compare_letters(
                self[k], other[k])
        return result

    def __invert__(self):
        """
        Inverse of ``self``.

        EXAMPLES::

            sage: F = FreeGroup('abc')
            sage: w = F('abCbA')
            sage: w.inverse()
            word: aBcBA
        """
        F = self.parent()
        A = F.alphabet()
        return F(A.inverse_letter(a) for a in reversed(self))

    inverse = __invert__

    def reduced(self):
        """
        Reduced form of ``self``.

        EXAMPLES::

            sage: F = FreeGroup(['a','b','c'])
            sage: w=F("abcAab")
            sage: w.reduced()
            word: abcb
        """
        result = list(self)

        F = self.parent()
        A = F.alphabet()

        i = 0
        j = 1
        long = len(result)
        while (j < long):
            k = 0
            while i - k >= 0 and j + k < long and \
                    A.are_inverse(result[i - k], result[j + k]):
                k = k + 1
            i = i - k + 1
            j = j + k + 1
            if j - 1 < long:
                result[i] = result[j - 1]
            else:
                i = i - 1
        return F(result[0:i + 1])

    def is_reduced(self):
        """
        ``True`` if ``self`` is a reduced word.

        EXAMPLES::

            sage: F= FreeGroupWord(3)
            sage: w=F("abcAab")
            sage: w.is_reduced()
            False
        """
        return all(self.parent().alphabet().are_inverse(
            self[i], self[i + 1]) for i in xrange(len(self) - 1))

    def is_identity(self, w):
        r"""
        ``True`` if ``self`` is the empty word.

        EXAMPLES::

            sage: F= FreeGroup(3)
            sage: w=F("abcACBAb")
            sage: w.is_identity()
            False

        """
        return len(w.reduced()) == 0

    def common_prefix_length(self, other):
        """

        Length of the common prefix of ``self`` and ``other``.

        WARNING:

        No reduction is performed, thus ``self`` and ``other`` are
        assumed to be reduced.

        EXAMPLES::

        sage: F=FreeGroup(3)
        sage: w=F("aBaa")
        sage: w.common_prefix_length("aBca")
        2

        """
        k = 0
        while(k < len(self) and k < len(other) and self[k] == other[k]):
            k = k + 1
        return k

    def is_prefix(self, other):
        """
        True if ``self`` is a prefix of ``other``.

       WARNING:

        No reduction is performed, thus ``self`` and ``other`` are
        assumed to be reduced.

        EXAMPLES::

        sage: F=FreeGroup(3)
        sage: F("aBaa").is_prefix("aBcb")
        False
        """
        i = 0
        l = len(self)
        if l <= len(other):
            done = False
            while i < l and not done:
                done = not self[i] == other[i]
                i = i + 1
            return not done
        else:
            return False

    def nielsen_strictly_less(self, other):
        """
        Determines wether ``self`` is strictly before ``other``
        in the Nielsen order.

        The Nielsen order is defined by u<v iff

             (len(u)<len(v))
          or
             (  len(u)==len(v)
              and
                (   u=u'u'', v=v'v''
                    u'<_lex v'
                 or
                    (u'=v' and u''<_lex v'')).

        Attended to be used in the Nielsen reduction algorithm.

        OUTPUT:

        - ``len(v)-len(u)`` if it is >0,

        - ``0`` if they have the same length, but ``u``<``v`` in the
          Nielsen order

        - ``-1`` if ``v=<u`` in the Nielsen order

        """
        l = len(self)
        result = len(other) - l
        if (result == 0):
            if (l == 0):
                result = -1
            else:
                if (l % 2 == 1):
                    half = (l + 1) / 2
                else:
                    half = l / 2
                uu = self[0:half]
                vv = other[0:half]
                if vv < uu:  # if vv<uu
                    result = -1
                elif vv == uu:  # now uu=vv
                    uuu = self[l - half:l]  # TODO: do not we have to compare
                    # self.inverse(uuu) and self.inverse(vvv) instead ?
                    vvv = other[l - half:l]
                    if vvv <= uuu:
                        result = -1  # if vvv<=uuu
        return result
