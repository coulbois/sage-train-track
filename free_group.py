#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.combinat.words.words import FiniteWords_over_OrderedAlphabet
from inverse_alphabet import AlphabetWithInverses
from free_group_word import FreeGroupWord


class FreeGroup(FiniteWords_over_OrderedAlphabet):
    """
    Free group of finite rank.

    EXAMPLES::

    sage: A=AlphabetWithInverses(['a','b'])
    sage: FreeGroup(A)
    Free group over ['a', 'b']

    sage: FreeGroup(3)
    Free group over ['a', 'b', 'c']

    sage: A=AlphabetWithInverses(2,type='x0')
    sage: FreeGroup(A)
    Free group over ['x0', 'x1']

    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version
    """
    def __init__(self,alphabet):
        if not isinstance(alphabet,AlphabetWithInverses):
            alphabet=AlphabetWithInverses(alphabet)
        FiniteWords_over_OrderedAlphabet.__init__(self,alphabet)

    def __repr__(self):
        """
        String representation for free group
        """
        return "Free group over %s" %str(self._alphabet.positive_letters())

    def __call__(self,data=None, length=None, datatype=None, caching=True, **kwds):
        if data==None: data=[]
        return FreeGroupWord(self,data)

    def reduced_product(self,u,v):
        """
        Returns the reduced product of u and v assuming that u and v
        are reduced.

        EXAMPLES::

            sage: FreeGroup(3).reduced_product("abAc","Caa")
            word: aba
        """
        i=0
        while (i<len(u) and i<len(v) and self._alphabet.are_inverse(u[-i-1],v[i])):
            i=i+1
        return self(u[:len(u)-i]+v[i:])

    def is_reduced(self,word):
        """
        Tests if the word is reduced.

        EXAMPLES::

            sage: A= AlphabetWithInverses(['a','b','c'])
            sage: F= FreeGroup(A)
            sage: w="abcAab"
            sage: print F.is_reduced(w)
            False
        """
        return all(self._alphabet.are_inverse(word[i],word[i+1]) for i in xrange(len(word)-1))

    def reduce(self,word):
        """
        Reduced form of ``word``.

        EXAMPLES::

            sage: F=FreeGroup(['a','b','c'])
            sage: w="abcAab"
            sage: print w," = ",F.reduce(w)
            abcAab = abcb
        """
        result = list(word)

        i=0
        j=1
        long=len(result)
        while (j<long):
            k=0
            while i-k>=0 and j+k<long and self._alphabet.are_inverse(result[i-k],result[j+k]): k=k+1
            i=i-k+1
            j=j+k+1
            if j-1<long:
                result[i]=result[j-1]
            else:
                i=i-1
        return self(result[0:i+1])

    def inverse_word(self,w):
        """
        Inverse of ``w``.

        EXAMPLES::

            sage: A = AlphabetWithInverse(['a','b','c'],['A','B','C'])
            sage: F=FreeGroup(A)
            sage: F.inverse('aBc')
            word: CbA
        """
        return self([self._alphabet.inverse_letter(a) for a in reversed(w)])

    def is_identity(self,w):
        r"""
        Tests whether the argument is trivial.
        """
        return len(self.reduce(w)) == 0

    def less(self,u,v):
        """
        True if u is before (or equal to) v in alphabetical order.

        WARNING:

        ``u`` and ``v`` are assumed to be reduced.

        EXAMPLES::

        sage: F=FreeGroup(3)
        sage: F.less("aba","abbb")
        True

        sage: F.less("aba","aba")
        True

        """
        result=False
        k=0
        while(k<len(u) and k<len(v) and u[k]==v[k]): k=k+1
        if (k==len(u)): result=True
        elif (k==len(v)): result=False
        else: result=self._alphabet.less_letter(u[k],v[k])
        return result

    def common_prefix_length(self,u,v):
        """
        Length of the common prefix of the words ``u`` and ``v``.

        WARNING:

        ``u`` and ``v`` are assumed to be reduced.

        EXAMPLES::

        sage: FreeGroup(3).common_prefix_length("aBaa","aBcb")
        2
        """
        k=0
        while(k<len(u) and k<len(v) and u[k]==v[k]): k=k+1
        return k

    def is_prefix(self,u,v):
        """
        True if ``u`` is a prefix of ``v``.

        EXAMPLES::

            sage: FreeGroup(3).is_prefix("aBaa","aBcb")
            False
        """
        i=0
        l=len(u)
        if l<=len(v):
            done=False
            while i<l and not done:
                done= not u[i]==v[i]
                i=i+1
            return not done
        else:
            return False

    def nielsen_strictly_less(self,u,v):
        """
        Determines wether ``u`` is strcitly before ``v`` in the Nielsen order
        used in the Nielsen reduction algorithm.

        OUTPUT:

        - ``len(v)-len(u)`` if it is >0,

        - ``0`` if they have the same length, but ``u``<``v`` in the
          Nielsen order

        - ``-1`` if ``v=<u`` in the Nielsen order

        Recall that u<v iff
             (len(u)<len(v))
          or
             (  len(u)==len(v)
              and
                (   u=u'u'', v=v'v''
                    u'<_lex v'
                 or
                    (u'=v' and u''<_lex v'')).
        """
        l=len(u)
        result=len(v)-l
        if (result==0):
            if (l==0):
                result=-1
            else:
                if (l%2==1):
                    half=(l+1)/2
                else: half=l/2
                uu=u[0:half]
                vv=v[0:half]
                if (not self.less(uu,vv)): # if vv<uu
                    result=-1
                elif (self.less(vv,uu)): # now uu=vv
                    uuu=u[l-half:l] #TODO: do not we have to compare self.inverse(uuu) and self.inverse(vvv) instead ?
                    vvv=v[l-half:l]
                    if (self.less(vvv,uuu)): result=-1 # if vvv<=uuu
        return result

    def identity_automorphism(self):
        """
        Identity automorphism of ``self``.
        """
        morph=dict((a,self([a])) for a in self._alphabet.positive_letters())

        from free_group_automorphism import FreeGroupAutomorphism #this has to be here and not in the preamble to prevent loop on import statements
        return FreeGroupAutomorphism(morph,group=self)

    def dehn_twist(self,a,b,on_left=False):
        """
        Dehn twist automorphism of ``self``.

        if ``on_left`` is ``False``: ``a -> ab``
        if ``on_left`` is ``True``: ``a -> ba``

        EXAMPLES

            sage: F=FreeGroup(3)
            sage: F.dehnt_twist('a','c')

            a->ac, b->b, c->c

            sage: F.dehn_twist('A','c')
            a->Ca,b->b,c->c
        """
        A = self.alphabet()

        if a not in A:
            raise ValueError("Letter %s not in alphabet" %str(a))
        if b not in A:
            raise ValueError("Letter %s not in alphabet" %str(b))
        if a == b:
            raise ValueError("Letter a=%s should be different from b=%s"%(str(a),str(b)))
        if A.are_inverse(a,b):
            raise ValueError("Letter a=%s should be different from the inverse of b=%s" %(str(a),str(b)))

        morphism = dict((letter,self([letter])) for letter in A.positive_letters())

        if A.is_positive_letter(a):
            if on_left:
                morphism[a] = self([b,a])
            else:
                morphism[a] = self([a,b])
        else:
            a = A.inverse_letter(a)
            b = A.inverse_letter(b)
            if on_left:
                morphism[a] = self([a,b])
            else:
                morphism[a] = self([b,a])
                
        from free_group_automorphism import FreeGroupAutomorphism
        return FreeGroupAutomorphism(morphism,group=self)

    def random_permutation(self):
        r"""
        Return a random permutation of ``self``.
        """
        from sage.misc.prandom import randint
        from sage.groups.perm_gps.permgroup_named import SymmetricGroup

        A = self.alphabet()
        P = A.positive_letters()
        s = SymmetricGroup(P).random_element()
        f = {}
        for a in P:
            if randint(0,1):
                f[a] = self([s(a)])
            else:
                f[a] = self([A.inverse_letter(s(a))])

        from free_group_automorphism import FreeGroupAutomorphism #this has to be here and not in the preamble to prevent loop on import statements
        return FreeGroupAutomorphism(f, group=self)

    def random_automorphism(self,length=1):
        """
        Random automorphism of ``self``.

        The output is a random word of given ``length`` on the set of Dehn twists.
        """
        if length==0: return self.identity_automorphism()

        A=self.alphabet()
        a=A.random_letter()
        b=A.random_letter([a,A.inverse_letter(a)])
        result=self.dehn_twist(a,b)
        for i in xrange(length-1):
            new_a=A.random_letter()
            if new_a==a:
                b=A.random_letter([a,A.inverse_letter(a),A.inverse_letter(b)])
            else:
                a=new_a
                b=A.random_letter([a,A.inverse_letter(a)])
            result *= self.dehn_twist(a,b)
        return result

    def _surface_dehn_twist_e(self,i):

        a=self._alphabet[2*i]
        b=self._alphabet[2*i+1]
        return self.dehn_twist(a,b,True)

    def _surface_dehn_twist_c(self,i):
        A=self._alphabet
        result=dict((a,self([a])) for a in A.positive_letters())
        result[A[2*i+1]]=self([A[2*i+2],A.inverse_letter(A[2*i]),A[2*i+1]])
        result[A[2*i+3]]=self([A[2*i+3],A[2*i],A.inverse_letter(A[2*i+2])])

        from free_group_automorphism import FreeGroupAutomorphism #this has to be here and not in the preamble to prevent loop on import statements
        return FreeGroupAutomorphism(result,group=self)

    def _surface_dehn_twist_m(self,i):
        A=self._alphabet
        result={}
        for j in xrange(2*i+1):
            result[A[j]]=self([A[j]])
        a=A[2*i]

        result[A[2*i+1]]=self([a,A[2*i+1]])
        aa=A.inverse_letter(a)
        for j in xrange(2*i+2,len(A)):
            result[A[j]]=self([a,A[j],aa])

        from free_group_automorphism import FreeGroupAutomorphism #this has to be here and not in the preamble to prevent loop on import statements
        return FreeGroupAutomorphism(result,group=self)

    def surface_dehn_twist(self,k):
        """
        Dehn twist of the surface (with one boundary component) with
        fundamental group ``self``.

        The surface is assumed to have genus g and 1 boundary
        component. The fundamental group has rank 2g, thus ``self`` is
        assumed to be of even rank.

        ``k`` is an integer 0<=k<3g-1.

        MCG(S_{g,1}) is generated by the Dehn twist along
        the curves:

        - g equators e_i,

        - g meridian m_i

        - g-1 circles c_i around two consecutive 'holes'.

        for 0<=k<g returns the Dehn twist along e_i with i=k

        for g<=k<2g returns the Dehn twist along m_i with i=k-g

        for 2g<=k<3g-1 returns the Dehn twist along c_i with i=k-2g

        The fundamental group has 2g generators. We fix the base point
        on the boundary. The generators are:

        - g x_i that turns around the i-th hole

        - g y_i that goes inside the i-th hole

        T_{e_i}: x_j-> x_j, x_i->y_ix_i, y_j->y_j

        T_{m_i}: x_j->x_j, y_j->y_j, j<i
                 x_i->x_i, y_i->x_iy_i
                 x_j->x_ix_jx_i\inv, y_j->x_iy_jx_i\inv

        T_{c_i}: x_j->x_j, y_j->y_j, y_i->x_{i+1}x_i\inv y_i, y_{i+1}->y_{i+1}x_{i+1}x_i\inv

        WARNING:

        ``self`` is assumed to be of even rank.

        """
        assert len(self._alphabet)%2==0

        g=len(self._alphabet)/2
        if (0<=k and k<g): result=self._surface_dehn_twist_e(k)
        elif (g<=k and k<2*g): result=self._surface_dehn_twist_m(k-g)
        elif (2*g<=k and k<3*g-1): result=self._surface_dehn_twist_c(k-2*g)

        return result



    def random_mapping_class(self,n=1):
        """
        Random mapping class of length (as a product of generating dehn twists)
        at most ``n``. `

        WARNING:

        The rank of ``self` is assumed to be even.
        """
        from sage.misc.prandom import randint

        assert len(self._alphabet)%2==0

        if n==0:
            return self.identity_automorphism()

        r=3*len(self._alphabet)/2-2
        i=randint(0,r)
        j=randint(0,1)
        if j==0:
            result=self.surface_dehn_twist(i)
        else:
            result=self.surface_dehn_twist(i).inverse()
        for ii in xrange(n-1):
            l=randint(0,1)
            if j==l:
                i=randint(0,r)
            else:
                k=randint(0,r-1)
                if k>=i: i=k+1
                j=l
            if j==0:
                result=result*self.surface_dehn_twist(i)
            else:
                result=result*self.surface_dehn_twist(i).inverse()
        return result

    def braid_automorphism(self,i,inverse=False):
        """
        Automorphism of ``self`` which corresponds to the generator
        sigma_i of the braid group.

        sigma_i: a_i -> a_i a_{i+1} a_i^{-1}
                 a_j -> a_j, for j!=i

        We assume 0<i<n, where n is the rank of ``self``.

        If ``inverse`` is True returns the inverse of sigma_i.

        """
        A=self._alphabet
        result=dict((a,self([a])) for a in A.positive_letters())
        if not inverse:
            a=A[i-1]
            result[a]=self([a,A[i],A.inverse_letter(a)])
            result[A[i]]=self([a])
        else:
            a=A[i]
            result[a]=self([A.inverse_letter(a),A[i-1],a])
            result[A[i-1]]=self(a)

        from free_group_automorphism import FreeGroupAutomorphism #this has to be here and not in the preamble to prevent loop on import statements
        return FreeGroupAutomorphism(result,group=self)

    def random_braid(self,n=1):
        """
        A random braid automorphism of ``self`` of length at most ``n``.
        """
        from sage.misc.prandom import randint

        A=self._alphabet
        if n==0:
            return self.identity_automorphism()
        i=randint(1,len(A)-1)
        j=randint(0,1)
        result=self.braid_automorphism(i,j!=0)
        for ii in xrange(n-1):
            l=randint(0,1)
            if l==j: i=randint(1,len(A)-1)
            else:
                k=randint(1,len(A)-2)
                if j<=k: i=k+1
            result *= self.braid_automorphism(i,j)
        return result
