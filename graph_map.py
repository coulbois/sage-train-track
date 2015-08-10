#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.combinat.words.morphism import WordMorphism
from sage.combinat.words.word import Word
from inverse_alphabet import AlphabetWithInverses

class GraphMap():
    """
    A GraphMap is a map from a Graph to another.  It maps a vertex to
    a vertex and an edge to an edge-path. It respects incidence
    relation. The inverse of an edge is send to the reverse path.

    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version
    """

    def __init__(self,*args):
        """
        The following forms are accepted:

        - ``GraphMap(f)`` where ``f`` is a ``GraphMap``.

        - ``GraphMap(domain,codomain,edge_map,vertex_map=None)`` where
          ``domain`` and ``codomain`` are ``GraphWithInverses`` and
          ``edge_map`` is anything accepted by
          ``WordMorphism(edge_map)`` with domain alphabet an
          AlphabetWithInverses (note that only one image of the pair
          (a,inverse_letter(a)) needs to be defined for each letter).
        """
        if isinstance(args[0],GraphMap):
            self._domain=args[0]._domain
            self._codomain=args[0]._codomain
            self._edge_map=args[0]._edge_map
            self._vertex_map=args[0]._vertex_map
        else:
            self._domain=args[0]
            self._codomain=args[1]
            self.set_edge_map(args[2])
            if len(args)>3:
                self._vertex_map=args[3]
        

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
        """A homotopy inverse of ``self``.

        For ``t1=self.domain().spanning_tree()`` and
        ``t2=self.codomain().spanning_tree()``. The alphabet ``A`` is
        made of edges not in ``t1`` identified (by their order in the
        alphabets of the domain and codomain) to letters not in
        ``t2``. The automorphism ``phi`` of ``FreeGroup(A)`` is
        defined using ``t1`` and ``t2``. The inverse map is given by
        ``phi.inverse()`` using ``t1`` and edges from ``t2`` are
        mapped to a single point (the root of ``t1``).

        In particular the inverse maps all vertices to the root of ``t1``.

        WARNING:

        ``self`` is assumed to be a homotopy equivalence.

        """

        from free_group import FreeGroup
        from free_group_automorphism import FreeGroupAutomorphism

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

        WARNING:

        It is assumed that ``self`` is a homotopy equivalence

        The result may send edges to trivial edge-paths.

        """
        G1=self.domain()
        A1=G1.alphabet()
        G2=self.domain()

        edge_map=dict((a,self.image(a)) for a in A1)

        done=False
        while not done:
            done=True
            prefix=dict() # the common prefix of all edges outgoing from the class of a vertex
            adjacent_vertex=dict() # a class of vertices linked by a tree which is contracted by self to a point
            for a in A1:
                u=edge_map[a]
                v=G1.initial_vertex(a)
                if len(u)>0:
                    if v not in adjacent_vertex:
                        adjacent_vertex[v]=set([v])
                    for w in adjacent_vertex[v]:
                        if w in prefix:
                            if len(prefix[w])>0:
                                p=G2.common_prefix_length(u,prefix[w])
                                prefix[w]=prefix[w][:p]
                            else:
                                prefix[w]=u
                else: #we need to increase the adjacent_vertex
                    vv=G1.terminal_vertex(a) #note that v!=vv because else the loop a is contracted contrary to homotopy equivalence
                    if v in adjacent_vertex and vv in adjacent_vertex:
                        adjacent_vertex[v].update(adjacent_vertex[vv])
                    elif v in adjacent_vertex:
                        adjacent_vertex[v].add(vv)
                    elif vv in adjacent_vertex:
                        adjacent_vertex[v]=adjacent_vertex[vv]
                        adjacent_vertex[v].add(v)
                    else:
                        adjacent_vertex[v]=set([v,vv])
                    if v in prefix:
                        prefixv=prefix[v]
                    else:
                        prefixv=False
                    for w in adjacent_vertex[v]:
                        if v!=w:
                            adjacent_vertex[w]=adjacent_vertex[v]
                            if w in prefix:
                                if prefixv:
                                    p=G2.common_prefix_length(prefixv,prefix[w])
                                    prefixv=prefixv[:p]
                                else:
                                    prefixv=prefix[w]
                    if prefixv:
                        for w in adjacent_vertex[v]:
                            prefix[w]=prefixv

            for a in A1:
                v=G1.initial_vertex(a)
                if v in prefix and len(prefix[v])>0:
                    done=False
                    aa=A1.inverse_letter(a)
                    if len(edge_map[a])>0:
                        edge_map[a]=edge_map[a][len(prefix[v]):]
                        edge_map[aa]=edge_map[aa][:-len(prefix[v])]
                    # else:
                    #     edge_map[a]=G2.reverse_path(prefix[v])
                    #     edge_map[aa]=prefix[v]
                    break

        self.set_edge_map(edge_map)

        return self


    def subdivide_domain(self, e):
        """
        Subdivide an edge in the domain graph. 

        The edge ``e`` is subdivided into ``l`` edges where ``l`` is
        the length of the image of ``e`` by ``self``.

        Update the edge map of ``self``.

        Intended to be used by Stalling's folding algorithm to get an
        immersion.

        SEE ALSO::

        GraphWithInverses.subdivide_edge()

        """
        G=self.domain()
        A = G.alphabet()
        result_map=dict((a,Word([a])) for a in A)
        w = self.image(e)
        new_edges=A.add_new_letters(len(w)-1)
        new_vertices=G.new_vertices(len(w)-1)
        d={(a,self.image(a)) for a in A.positive_letters()}
        for i,a in enumerate(new_edges):
            v=new_vertices[i]
            if i==0:
                vi=G.initial_vertex(e)
                vt=G.terminal_vertex(e)
                f=new_edges[i][0]
                ee=A.inverse_letter(e)
                ff=new_edges[i][1]
                G.set_terminal_vertex(e,v)
                G.add_edge(v,vt,[f,ff])
                result_map[e]=result_map[e]*Word([f])
                result_map[ee]=Word([ff])*result_map[ee]
                d[a[0]] = w[i+1]
            else:
                vi=self._domain.initial_vertex(new_edges[i-1][0])
                vt=self._domain.terminal_vertex(new_edges[i-1][0])
                f=new_edges[i][0]
                #ee=A.inverse_letter(e) #already done
                ff=new_edges[i][1]
                self._domain.set_terminal_vertex(new_edges[i-1][0],v)
                self._domain.add_edge(v,vt,[f,ff])
                result_map[e]=result_map[e]*Word([f])
                result_map[ee]=Word([ff])*result_map[ee]
                d[a[0]] = w[i+1]
                    
        # updating self.edge_map after subdivision
        if A.is_positive_letter(e):
            d[e] = Word([self.image(e)[0]])
        else:
            d[ee]=Word([self.image(ee)[-1]])

        self.set_edge_map(d)
                                   
        return result_map
        
    def illegal_turns(self,turns=None):
        """
        List of illegal turns in the domain graph.

        A turn is illegal if it is mapped by ``self`` to a degenerate
        turn.

        INPUT:

        ``turns`` a list of turns of the domain graph. Default is None
        meaning all the turns of the graph. I not ``None`` return the
        sublist of ``turns`` consisting of illegal turns.
        """
        result = []

        if turns is None:
            turns=self.domain().turns()

        for turn in turns:
            u=self.image(turn[0])
            v=self.image(turn[1])
            if len(u)==0 or len(v)==0 or u[0]==v[0]:
                result.append(turn)
        return result
        

    def stallings_folding(self):
        """
        Implement Stallings' folding to get an immersion from ``self``. 

        The domain of ``self`` is fold until we get an immersion. 

        ALGORITHM:

        We first subdivide edges of the domain according to length of
        their image.  

        Then fold one gate at one vertex and update the edge map and
        illegal turns list. 

        Repeat the process till no illegal turns remain.

        REFERENCES:

        [Stallings] J. Stallings, Topology of Finite Graphs,
        """
        A = self.domain().alphabet()
        for a in A:
            if len(self.image(a)) >1:
                self.subdivide_domain(a)
                
        Turns = self._domain.turns() #list of all turns in domain after subdivision
        Il_turns = self.illegal_turns(Turns) # list of illegal turns in domain after subdivision    
        counter = 0
        while len(Il_turns)>0:
            counter = counter +1
            
            # find edge_list (list of edges in the gate correspoding to e1) to fold at exactly one vertex
            e1=Il_turns[0][0]
            edge_list = [e1]
            for a in A:
                if self._domain.initial_vertex(a) == self._domain.initial_vertex(e1) and e1!=a:
                    if (e1,a) in Il_turns or (a,e1) in Il_turns:
                        edge_list.append(a) 
                        
            edge_list = list(set(edge_list)) # remove duplicates 
            # fold at initial_vertex of e1 ( this function updates the domain and edge_map)         
            self._domain.fold(edge_list,[])
                
            #update edge_map again 
            d={}
            d[edge_list[0]] = self.image(edge_list[0])
            for a in A:
                if a not in edge_list:
                    d[a] = self.image(a)
            wm = WordMorphism(d)
            self.set_edge_map(wm)    
            Turns = self._domain.turns() #update list of all turns in domain 
            Il_turns = self.illegal_turns(Turns) # update list of illegal turns in domain 
                 
        
        return self
        
        
    def pullback(self,f2,G3,A):
        """
        INPUT : Two Graph maps f1:G1->G, f2:G2->G, an empty GraphWithInverses G3 and an empty AlphabetWithInverses A
        OPERATION : Find the pullback G3 and a graph map f:G3->G
        OUTPUT : Graphmap f 
        
        The pullback method can be used to find intersection of two subgroups of a Free Group. 
        
        Example : 
        G1 = GraphWithInverses.rose_graph(AlphabetWithInverses(2,type='x0')) 
        G2 = GraphWithInverses.rose_graph(AlphabetWithInverses(2,type='a0')) 
        G =  GraphWithInverses.rose_graph(AlphabetWithInverses(2)) 
        n1 = WordMorphism({'x0':['a','a'],'x1':['b','a']})
        n2 = WordMorphism({'a0':['b','a'],'a1':['b','b','b','a','B','a']})
        f1 = GraphMap(G1,G,n1)
        f2 = GraphMap(G2,G,n2)
        G3 = GraphWithInverses()
        A = AlphabetWithInverses(0,type='a0')
        
        f1.pullback(f2,G3,A)
        """
        import itertools
        #First convert self and f2 into immersions
        self.stallings_folding()
        f2.stallings_folding()
        
        # G3 = GraphWithInverses()
        #A = AlphabetWithInverses(0,type='a0')
        d={}
        #get set of vertices 
        V = []
        for i in itertools.product(self.domain().vertices(),f2.domain().vertices()):
            V.append(i)

        #add edges 
        for v in V:
            for w in V:
                for e1 in self.domain().alphabet().positive_letters():
                    if self.domain().initial_vertex(e1) == v[0] and self.domain().terminal_vertex(e1) == w[0]:
                        for e2 in f2.domain().alphabet().positive_letters():
                            if f2.domain().initial_vertex(e2) == v[1] and f2.domain().terminal_vertex(e2) == w[1]:
                                if self.image(e1)==f2.image(e2):                                
                                    e = A.add_new_letter()
                                    G3.add_edge(v,w,e )
                                    #update dictionary to define map on G3
                                    d[e[0]] = self.image(e1) 
                                    
        G3._alphabet = A
        n3 = WordMorphism(d)
        G = self.codomain() #same as f2.codomain()
        
        return GraphMap(G3,G,n3)    
        
    @staticmethod
    def rose_map(automorphism):
        """
        The graph map of the rose representing the automorphism.

        The rose is built on a copy of the alphabet of the domain of
        ``automorphism``.
        """

        graph=GraphWithInverses.rose_graph(automorphism.domain().alphabet().copy())
        return GraphMap(graph,graph,automorphism)

