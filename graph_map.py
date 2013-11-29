#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from sage.combinat.words.morphism import WordMorphism

class GraphMap():
    """
    A GraphMap is a map from a Graph to another .  It maps a vertex to
    a vertex and an edge to an edge-path. It respects incidence
    relation. The inverse of an edge is send to the reverse path.

    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version
    """

    def __init__(self,domain,codomain,edge_map,vertex_map=None):
        self._domain=domain
        self._codomain=codomain
        self.set_edge_map(edge_map)
        self._vertex_map=vertex_map

    def __call__(self,argument):
        """
        Applies ``self`` to ``argument`` which is either a vertex of ``self`` or
        an edge path.

        SEE ALSO:

        To compute the image of a letter of the alphabet use
        ``self.image(a)``.
        """
        if self._domain.has_vertex(argument):
            if self._vertex_map==None:
                self.update_vertex_map()

            return self._vertex_map[argument]
        else:
            return self._codomain.reduce_path(self._edge_map(argument))

    def __mul__(self,other):
        """
        Compose ``self`` with ``other``.
        """
        A=other._domain.alphabet()
        result_map={}
        for a in A.positive_letters():
            result_map[a]=self(other._edge_map.image(a))
        return GraphMap(other._domain,self._codomain,result_map)


    def __str__(self):
        """
        String represetation of ``self``.
        """
        result="Graph map:\n"+self._domain.__str__()+"\n"
        result+=self._codomain.__str__()+"\n"
        result=result+"edge map: "
        for a in self._domain._alphabet.positive_letters(): result+=a+"->"+self.image(a).__str__()+", "
        result=result[:-2]+"\n"
        if self._vertex_map!=None:
            result=result+"vertex map: "+self._vertex_map.__str__()+"\n"
        return result

    def domain(self):
        """
        Domain of ``self``: this is a graph.
        """
        return self._domain

    def codomain(self):
        """
        Codomain of ``self``: this is a graph.
        """
        return self._codomain

    def set_edge_map(self,edge_map):
        """
        Sets the edge map of ``self``.

        ``edge_map`` is anything that is accepted by
        ``Wordmorphism(edge_map)``, the image of the inverse letters
        will be calculated: they need not be explicit in ``edge_map``,
        only one of the images of each pair [letter,inverse(letter)]
        need to be given by ``edge_map``. Images of ``edge_map`` need
        not be reduced.

        """
        A=self.domain().alphabet()
        tmp_map=WordMorphism(edge_map)
        m={}
        for a in tmp_map._domain.alphabet():
            m[a]=self._codomain.reduce_path(tmp_map.image(a))
            m[A.inverse_letter(a)]=self._codomain.reverse_path(m[a])
        self._edge_map=WordMorphism(m)
        self._vertex_map=None

    def compose_edge_map(self,edge_morph):
        """
        Compose ``self`` with the morphism ``edge_morph``.

        Update the edge_map of ``self`` with (``edge_morph`` o ``self``).
        """
        edge_map=dict((a,edge_morph(self._edge_map.image(a))) for a in self._domain._alphabet.positive_letters())
        self.set_edge_map(edge_map)

    def update_vertex_map(self):
        """
        Computes the vertex map of ``self`` from its edge map.
        """
        vertex_map={}
        for e in self._domain._alphabet.positive_letters():
            p=self.image(e)
            if len(p)>0:
                vertex_map[self._domain.initial_vertex(e)]=self._codomain.initial_vertex(p[0])
                vertex_map[self._domain.terminal_vertex(e)]=self._codomain.terminal_vertex(p[-1])
        self._vertex_map=vertex_map

    def edge_map(self):
        """
        The edge map of ``self``: this is a word morphism.
        """
        return self._edge_map

    def image(self,letter,iter=1):
        """
        The image of a letter.

        if ``iter>1`` then returns ``self^iter(letter)``
        """

        if iter==1:
            return self._edge_map.image(letter)
        else:
            return self._codomain.reduce_path(self._edge_map(self._edge_map(letter),iter-1))

    def inverse(self):
        """
        A homotopy inverse of ``self``.

        WARNING:

        ``self`` is assumed to be a homotopy equivalence.
        """


        G1=self.domain()
        A1=G1.alphabet()
        t1=G1.spanning_tree()

        G2=self.codomain()
        A2=G2.alphabet()
        t2=G2.spanning_tree()

        A=AlphabetWithInverses(len(A1)-len(G1.vertices())+1)
        F=FreeGroup(A)

        map=dict()
        translate=dict()

        i=0
        for a in A1.positive_letters():
            l=len(t1[G1.initial_vertex(a)])-len(t1[G1.terminal_vertex(a)])
            if (l!=1 or t1[G1.initial_vertex(a)][-1]!=A1.inverse_letter(a)) and\
                    (l!=-1 or t1[G1.terminal_vertex(a)][-1]!=a): # a is not in the spanning tree
                map[A[i]]=self(t1[G1.initial_vertex(a)]*Word([a])*G1.reverse_path(t1[G1.terminal_vertex(a)]))
                translate[A[i]]=a
                translate[A.inverse_letter(A[i])]=A1.inverse_letter(a)
                i+=1

        rename=dict()
        edge_map=dict()

        i=0
        for a in A2.positive_letters():
            l=len(t2[G2.initial_vertex(a)])-len(t2[G2.terminal_vertex(a)])
            if (l!=1 or t2[G2.initial_vertex(a)][-1]!=A2.inverse_letter(a)) and\
                    (l!=-1 or t2[G2.terminal_vertex(a)][-1]!=a): # a is not in the spanning tree
                rename[a]=A[i]
                rename[A2.inverse_letter(a)]=A.inverse_letter(A[i])
                i+=1
            else:
                edge_map[a]=Word()

        for a in map:
            map[a]=F([rename[b] for b in map[a] if b in rename])

        phi=FreeGroupAutomorphism(map,F)
        psi=phi.inverse()

        i=0
        for a in A2.positive_letters():
            if a not in edge_map:
                result=Word()
                for b in psi.image(A[i]):
                    c=translate[b]
                    result=result*t1[G1.initial_vertex(c)]*Word([c])*G1.reverse_path(t1[G1.terminal_vertex(c)])
                edge_map[a]=G1.reduce_path(result)
                i+=1

        return GraphMap(G2,G1,edge_map)


    def tighten(self):
        """
        Tighten ``self`` such that there are at least two gates at
        each vertex of the domain.

        A map is tight if for each vertex ``v`` of the domain, there
        exist reduced edge paths ``u`` and ``v`` in the domain with
        ``self(u)`` and ``self(v)`` non-trivial reduced paths starting
        with different edges.

        ``self`` and ``self.tighten()`` are homotopic.

        """
        G1=self.domain()
        A1=G1.alphabet()
        G2=self.domain()

        edge_map=dict((a,self.image(a)) for a in A1)

        done=False
        while not done:
            done=True
            prefix=dict()
            for a in A1:
                u=edge_map[a]
                v=G1.initial_vertex(a)
                if len(u)>0:
                    if v in prefix:
                        if len(prefix[v])>0:
                            p=G2.common_prefix_length(u,prefix[v])
                            prefix[v]=prefix[v][:p]
                    else:
                        prefix[v]=u

            for a in A1:
                v=G1.initial_vertex(a)
                if v in prefix and len(prefix[v])>0:
                    done=False
                    aa=A1.inverse_letter(a)
                    if len(edge_map[a])>0:
                        edge_map[a]=edge_map[a][len(prefix[v]):]
                        edge_map[aa]=edge_map[aa][:-len(prefix[v])]
                    else:
                        edge_map[a]=G2.reverse_path(prefix[v])
                        edge_map[aa]=prefix[v]

        self.set_edge_map(edge_map)

        return self

    @staticmethod
    def rose_map(automorphism):
        """
        The graph map of the rose representing the automorphism.

        The rose is built on a copy of the alphabet of the domain of
        ``automorphism``.
        """

        graph=GraphWithInverses.rose_graph(automorphism.domain().alphabet().copy())
        return GraphMap(graph,graph,automorphism)

