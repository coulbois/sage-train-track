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
        Applies self to argument which is either a vertex of self or
        an edge path. To compute the image of a letter of the alphabet
        use self.image(a).
        """
        if self._domain.has_vertex(argument):
            if self._vertex_map==None:
                self.update_vertex_map()
                
            return self._vertex_map[argument]
        else:
            return self._codomain.reduce_path(self._edge_map(argument))

    def __mul__(self,other):
        """
        Compose two GraphMap.
        """
        A=other._domain._alphabet
        result_map={}
        for a in A.positive_letters():
            result_map[a]=self(other._edge_map.image(a))
        return GraphMap(other._domain,self._codomain,result_map)

    
    def __str__(self):
        """
        String represetation of self.
        """
        result="Graph map:\n"+self._domain.__str__()
        result+=self._codomain.__str__()
        result=result+"edge map: "
        for a in self._domain._alphabet.positive_letters(): result+=a+"->"+self.image(a).__str__()+", "
        result=result[:-2]+"\n"
        if vertex_map!=None:
            result=result+"vertex map: "+self._vertex_map.__str__()+"\n"
        return result
           
    def domain(self):
        """
        The domain of self: this is a graph.
        """
        return self._domain

    def codomain(self):
        """
        The codomain of self: this is a graph.
        """
        return self._codomain

    def set_edge_map(self,edge_map):
        """
        Sets the edge map of self. 

        edge_map is anything that is accepted by
        Wordmorphism(edge_map), the image of the inverse letters will
        be calculated: they need not be explicit in edge_map.

        """
        A=self._domain._alphabet
        tmp_map=WordMorphism(edge_map)
        m={}
        for a in tmp_map._domain._alphabet:
            m[a]=self._codomain.reduce_path(tmp_map.image(a))
            m[A.inverse_letter(a)]=self._codomain.reverse_path(m[a])
        self._edge_map=WordMorphism(m)
        self._vertex_map=None

    def compose_edge_map(self,edge_morph):
        """
        Compose self with the morphism edge_morph and update the
        edge_map of self with edge_morph o self.
        """
        edge_map=dict((a,edge_morph(self._edge_map.image(a))) for a in self._domain._alphabet.positive_letters())
        self.set_edge_map(edge_map)

    def update_vertex_map(self):
        vertex_map={}
        for e in self._domain._alphabet.positive_letters():
            p=self.image(e)
            if len(p)>0:
                vertex_map[self._domain.initial_vertex(e)]=self._codomain.initial_vertex(p[0])
                vertex_map[self._domain.terminal_vertex(e)]=self._codomain.terminal_vertex(p[-1])
        self._vertex_map=vertex_map
        
    def edge_map(self):
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

    @staticmethod
    def rose_map(automorphism):
        """
        Returns the graph map of the rose on a copy of the alphabet
        corresponding to the automorphism.
        """

        graph=GraphWithInverses.rose_graph(automorphism._domain._alphabet.copy())
        return GraphMap(graph,graph,automorphism)

