r"""
inverse_graph module, define Class for GraphWithInverses and MetricGraph

AUTHORS:

- Thierry COULBOIS (2013-01-01): initial version

- Dominique BENIELLI (2016-02_15):
  AMU University <dominique.benielli@univ-amu.fr>, Integration in SageMath

EXAMPLES::

    sage: G = GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
    sage: A = AlphabetWithInverses(2)
    sage: H = GraphWithInverses.rose_graph(A)
    sage: print GraphMap(G,H,"a->ab,b->b,c->B")
    Graph map:
    a: 0->0, c: 1->0, b: 0->1
    a: 0->0, b: 0->0
    edge map: a->ab, c->B, b->b
"""
#
# *****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# *****************************************************************************
from sage.combinat.words.morphism import WordMorphism
from sage.combinat.words.word import Word
from sage.combinat.words.inverse_alphabet import AlphabetWithInverses
from sage.combinat.words.inverse_graph import GraphWithInverses


class GraphMap:
    """
    A GraphMap is a map from a Graph to another.  It maps a vertex to
    a vertex and an edge to an edge-path. It respects incidence
    relation. The inverse of an edge is send to the reverse path.

    AUTHORS:

    - Thierry Coulbois (2013-05-16): beta.0 version
    """

    def __init__(self, *args):
        """
        The following forms are accepted:

        - ``GraphMap(f)`` where ``f`` is a ``GraphMap``.
        - ``GraphMap(domain, codomain, edge_map, vertex_map=None)`` where
          ``domain`` and ``codomain`` are ``GraphWithInverses`` and
          ``edge_map`` is anything accepted by
          ``WordMorphism(edge_map)`` with domain alphabet an
          AlphabetWithInverses (note that only one image of the pair
          (a,inverse_letter(a)) needs to be defined for each letter).

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: print GraphMap(G,H,"a->ab,b->b,c->B")
            Graph map:
            a: 0->0, b: 0->1, c: 1->1
            a: 0->0, b: 0->0
            edge map: a->ab, b->b, c->B
        """
        if isinstance(args[0], GraphMap):
            self._domain = args[0]._domain
            self._codomain = args[0]._codomain
            self._edge_map = args[0]._edge_map
            self._vertex_map = args[0]._vertex_map
        else:
            self._domain = args[0]
            self._codomain = args[1]
            self.set_edge_map(args[2])
            if len(args) > 3:
                self._vertex_map = args[3]

    def __call__(self, argument):
        """
        Applies ``self`` to ``argument`` which is either a vertex
         of ``self`` or an edge path.

        INPUT:

        -``argument`` a vertex of ``self`` or a edge path

        OUTPUT:

        A vertex of ``self`` or an edge path
        Applies ``self`` to ``argument`` which is either .

        .. SEEALSO:

            To compute the image of a letter of the alphabet use
            ``self.image(a)``.

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->ab,b->b,c->B")
            sage: f('abc')
            word: ab
        """
        if self._domain.has_vertex(argument):
            if self._vertex_map is None:
                self.update_vertex_map()

            return self._vertex_map[argument]
        else:
            return self._codomain.reduce_path(self._edge_map(argument))

    def __mul__(self, other):
        """
        Compose ``self`` with ``other``.

        INPUT:

        - ``other`` -- other GraphMap to compute multiplication

        OUTPUT:

        GraphMap obtains with other domain as first
        input and ``self`` codomain for second input and vertex_map is
        construct applying ``self`` to ``other`` edge_map image

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->ab,b->b,c->B")
            sage: g = GraphMap(H,H,"a->aba,b->ba")
            sage: print g * f
            Graph map:
            a: 0->0, b: 0->1, c: 1->1
            a: 0->0, b: 0->0
            edge map: a->ababa, b->ba, c->AB
        """
        A = other._domain.alphabet()
        result_map = {}
        for a in A.positive_letters():
            result_map[a] = self(other._edge_map.image(a))
        return GraphMap(other._domain, self._codomain, result_map)

    def __repr__(self):
        """
        String represetation of ``self``.

        OUTPUT:

        a string representation of ``self``

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: GraphMap(G,H,"a->ab,b->b,c->B").__repr__()
            'Graph map:\na: 0->0, b: 0->1, c: 1->1\na: 0->0, b: 0->0\nedge map: a->ab, b->b, c->B'
        """
        result = "Graph map:\n" + self._domain.__str__() + "\n"
        result += self._codomain.__str__() + "\n"
        result += "edge map: "
        for a in self._domain._alphabet.positive_letters():
            result += a + "->" + self.image(a).__str__() + ", "
        result = result[:-2] # + "\n"
        if self._vertex_map is not None:
            result = result + "\n"
            result = result + "vertex map: " +\
                self._vertex_map.__str__() # + "\n"
        return result

    def domain(self):
        """
        Domain of ``self``: this is a graph.

        OUTPUT:

        Domain of ``self`` which is a GrapMap

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->ab,b->b,c->B")
            sage: print f.domain()
            a: 0->0, b: 0->1, c: 1->1
        """
        return self._domain

    def codomain(self):
        """
        Codomain of ``self``: this is a graph.

        OUTPUT:

        Codomain of ``self`` which is a GrapMap

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->ab,b->b,c->B")
            sage: print f.codomain()
            a: 0->0, b: 0->0
        """
        return self._codomain

    def set_edge_map(self, edge_map):
        """
        Sets the edge map of ``self``.

        ``edge_map`` is anything that is accepted by
        ``WordMorphism(edge_map)``, the image of the inverse letters
        will be calculated: they need not be explicit in ``edge_map``,
        only one of the images of each pair [letter,inverse(letter)]
        need to be given by ``edge_map``. Images of ``edge_map`` need
        not be reduced.

        INPUT:

        - ``edge_map`` -- anything which is accepted by ``WordMorphism(edge_map)``

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->ab,b->b,c->B")
            sage: f.set_edge_map('a->b,b->,c->b')
            sage: print f
            Graph map:
            a: 0->0, b: 0->1, c: 1->1
            a: 0->0, b: 0->0
            edge map: a->b, b->, c->b
        """
        A = self.domain().alphabet()
        tmp_map = WordMorphism(edge_map)
        m = {}
        for a in tmp_map._domain.alphabet():
            m[a] = self._codomain.reduce_path(tmp_map.image(a))
            m[A.inverse_letter(a)] = self._codomain.reverse_path(m[a])
        self._edge_map = WordMorphism(m)
        self._vertex_map = None

    def compose_edge_map(self, edge_morph):
        """Compose ``self`` with the morphism ``edge_morph``.

        Update the edge_map of ``self`` with (``edge_morph`` o ``self``).
        
        INPUT:

        - ``edge_morph`` -- A ``WordMorphism`` from the alphabet labeling
          the codomain of ``self`` to itself.

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->ab,b->b,c->B")
            sage: f.compose_edge_map(FreeGroupAutomorphism('a->aba,b->ba'))
            sage: print f
            Graph map:
            a: 0->0, b: 0->1, c: 1->1
            a: 0->0, b: 0->0
            edge map: a->ababa, b->ba, c->AB
        """
        edge_map = dict((a, edge_morph.to_word_morphism(use_str=True, upper_case_as_inverse=True)(self._edge_map.image(a))) for a in
                        self._domain._alphabet.positive_letters())
        self.set_edge_map(edge_map)

    def update_vertex_map(self):
        """
        Computes the vertex map of ``self`` from its edge map.

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->ab,b->b,c->B")
            sage: f.update_vertex_map()
            sage: print f
            Graph map:
            a: 0->0, b: 0->1, c: 1->1
            a: 0->0, b: 0->0
            edge map: a->ab, b->b, c->B
            vertex map: {0: 0, 1: 0}
        """
        vertex_map = {}
        for e in self._domain._alphabet.positive_letters():
            p = self.image(e)
            if len(p) > 0:
                vertex_map[self._domain.initial_vertex(e)] = \
                    self._codomain.initial_vertex(p[0])
                vertex_map[self._domain.terminal_vertex(e)] = \
                    self._codomain.terminal_vertex(p[-1])
        self._vertex_map = vertex_map

    def edge_map(self):
        """
        The edge map of ``self``: this is a word morphism.

        OUTPUT:

        The edge map of ``self``

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->ab,b->b,c->B")
            sage: f.edge_map()
            WordMorphism: A->BA, B->B, C->b, a->ab, b->b, c->B
        """
        return self._edge_map

    def image(self, letter, iter=1):
        """The image of a letter.

        if ``iter>1`` then returns ``self^iter(letter)``

        INPUT:
            
        - ``iter`` (default: 1) -- a positive integer
        - ``letter`` -- a letter of the alphabet of the domain of ``self``.

        OUTPUT:

        if ``iter`` > 1 then returns ``self``^iter(letter)``
        if ``iter`` = 1then returns the image of letter

        .. WARNING::

            ``iter`` may be greater than 1 only if the domain and codomain
            of ``self`` are equal (that is to say, ``self`` is a
            GraphSelfMap)

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->ab,b->b,c->B")
            sage: f.image('a')
            word: ab
        """
        if iter == 1:
            return self._edge_map.image(letter)
        else:
            return self._codomain.reduce_path(
                self._edge_map(self._edge_map(letter), iter - 1))

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

        OUTPUT:

        A homotopy inverse of ``self``.

        .. WARNING::

            ``self`` is assumed to be a homotopy equivalence.

        EXAMPLES::

            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: A = AlphabetWithInverses(2)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->ab,b->b,c->B")
            sage: print f.inverse()
            Graph map:
            a: 0->0, b: 0->0
            a: 0->0, b: 0->1, c: 1->1
            edge map: a->abcB, b->bCB
        """

        from sage.groups.free_group import FreeGroup
        from free_group_automorphism import FreeGroupAutomorphism

        G1 = self.domain()
        A1 = G1.alphabet()
        T1 = G1.spanning_tree()

        G2 = self.codomain()
        A2 = G2.alphabet()
        T2 = G2.spanning_tree()

        A = AlphabetWithInverses(len(A1) - len(G1.vertices()) + 1)
        F = FreeGroup(A.positive_letters())

        map = dict()
        translate = dict()

        i = 0
        for a in A1.positive_letters():
            l = len(T1[G1.initial_vertex(a)]) - len(T1[G1.terminal_vertex(a)])
            if (l != 1 or T1[G1.initial_vertex(a)][-1] != A1.inverse_letter(
                    a)) and (l != -1 or T1[G1.terminal_vertex(a)][-1] != a):
                # a is not in the spanning tree
                map[A[i]] = self(
                    T1[G1.initial_vertex(a)] * Word([a]) * G1.reverse_path(
                        T1[G1.terminal_vertex(a)]))
                translate[A[i]] = a
                translate[A.inverse_letter(A[i])] = A1.inverse_letter(a)
                i += 1
        rename = dict()
        edge_map = dict()

        i = 0
        for a in A2.positive_letters():
            l = len(T2[G2.initial_vertex(a)]) - len(T2[G2.terminal_vertex(a)])
            if (l != 1 or T2[G2.initial_vertex(a)][-1] != A2.inverse_letter(
                    a)) and (l != -1 or T2[G2.terminal_vertex(a)][-1] != a):
                # a is not in the spanning tree
                rename[a] = A[i]
                rename[A2.inverse_letter(a)] = A.inverse_letter(A[i])
                i += 1
            else:
                edge_map[a] = Word()

        for a in map:
            map[a] = F([rename[b] for b in map[a] if b in rename])

        phi = FreeGroupAutomorphism(map, F)
        psi = phi.inverse()
        i = 0
        for a in A2.positive_letters():
            if a not in edge_map:
                result = Word()
                for b in psi(A[i]).to_word():
                    c = translate[b]
                    result = result * T1[G1.initial_vertex(c)] * Word(
                        [c]) * G1.reverse_path(T1[G1.terminal_vertex(c)])
                edge_map[a] = G1.reduce_path(result)
                i += 1

        return GraphMap(G2, G1, edge_map)

    def tighten(self):
        """
        Tighten ``self`` such that there are at least two gates at
        each vertex of the domain.

        A map is tight if for each vertex ``v`` of the domain, there
        exist reduced edge paths ``u`` and ``v`` in the domain with
        ``self(u)`` and ``self(v)`` non-trivial reduced paths starting
        with different edges.

        ``self`` and ``self.tighten()`` are homotopic.

        OUTPUT:

        Tighten ``self`` such that there are at least two gates at
        each vertex of the domain.

        .. WARNING::

            It is assumed that ``self`` is a homotopy equivalence

        The result may send edges to trivial edge-paths.

        EXAMPLES::

            sage: A = AlphabetWithInverses(2)
            sage: G = GraphWithInverses.rose_graph(A)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->baabAB,b->babAB")
            sage: f.tighten()
            WordMorphism: A->BA, B->B, a->ab, b->b
            sage: print f
            Graph map:
            a: 0->0, b: 0->0
            a: 0->0, b: 0->0
            edge map: a->ab, b->b
        """
        G1 = self.domain()
        A1 = G1.alphabet()
        G2 = self.codomain()

        edge_map = dict((a, self.image(a)) for a in A1)

        done = False
        while not done:
            done = True
            prefix = dict()  # the common prefix of all edges outgoing from
            # the class of a vertex
            adjacent_vertex = dict()  # a class of vertices linked by a tree
            # which is contracted by self to a point
            for a in A1:
                u = edge_map[a]
                v = G1.initial_vertex(a)
                if len(u) > 0:
                    if v not in adjacent_vertex:
                        adjacent_vertex[v] = set([v])
                    for w in adjacent_vertex[v]:
                        if w in prefix:
                            if len(prefix[w]) > 0:
                                p = G2.common_prefix_length(u, prefix[w])
                                prefix[w] = prefix[w][:p]
                        else:
                            prefix[w] = u
                else:  # we need to increase the adjacent_vertex
                    vv = G1.terminal_vertex(a)
                    # note that v!=vv because else the loop a is contracted
                    # contrary to homotopy equivalence
                    if v in adjacent_vertex and vv in adjacent_vertex:
                        adjacent_vertex[v].update(adjacent_vertex[vv])
                    elif v in adjacent_vertex:
                        adjacent_vertex[v].add(vv)
                    elif vv in adjacent_vertex:
                        adjacent_vertex[v] = adjacent_vertex[vv]
                        adjacent_vertex[v].add(v)
                    else:
                        adjacent_vertex[v] = set([v, vv])
                    if v in prefix:
                        prefixv = prefix[v]
                    else:
                        prefixv = False
                    for w in adjacent_vertex[v]:
                        if v != w:
                            adjacent_vertex[w] = adjacent_vertex[v]
                            if w in prefix:
                                if prefixv:
                                    p = G2.common_prefix_length(prefixv,
                                                                prefix[w])
                                    prefixv = prefixv[:p]
                                else:
                                    prefixv = prefix[w]
                    if prefixv:
                        for w in adjacent_vertex[v]:
                            prefix[w] = prefixv
            
            for a in A1:
                v = G1.initial_vertex(a)
                if v in prefix and len(prefix[v]) > 0:
                    done = False
                    aa = A1.inverse_letter(a)
                    if len(edge_map[a]) > 0:
                        edge_map[a] = edge_map[a][len(prefix[v]):]
                        edge_map[aa] = edge_map[aa][:-len(prefix[v])]

        self.set_edge_map(edge_map)

        return self._edge_map

    def subdivide_domain(self, e):
        """
        Subdivide an edge in the domain graph.

        The edge ``e`` is subdivided into ``l`` edges where ``l`` is
        the length of the image of ``e`` by ``self``.

        Update the edge map of ``self``.

        Intended to be used by Stalling's folding algorithm to get an
        immersion.

        ...SEE ALSO::

            :meth:`sage.combinat.words.inverse_graph.GraphWithInverses.subdivide_edge()`

        INPUT:

        - ``e`` -- and edge of the domain of ``self``.

        OUTPUT:

        A dictionnary that maps old edges of the domain to new edges of the domain.

        EXAMPLES::

            sage: A = AlphabetWithInverses(2)
            sage: G = GraphWithInverses.rose_graph(A)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->aba,b->ab")
            sage: f.subdivide_domain('a')
            {'A': word: DCA, 'B': word: B, 'a': word: acd, 'b': word: b}
            sage: print f
            Graph map:
            a: 0->1, b: 0->0, c: 1->2, d: 2->0
            a: 0->0, b: 0->0
            edge map: a->a, b->ab, c->b, d->a
        """
        G = self.domain()
        A = G.alphabet()
        result_map = dict((a, Word([a])) for a in A)
        w = self.image(e)
        d = dict((a, self.image(a)) for a in A.positive_letters())
        new_edges = A.add_new_letters(len(w) - 1)
        new_vertices = G.new_vertices(len(w) - 1)
        for i, a in enumerate(new_edges):
            v = new_vertices[i]
            if i == 0:
                vi = G.initial_vertex(e)
                vt = G.terminal_vertex(e)
                f = new_edges[i][0]
                ee = A.inverse_letter(e)
                ff = new_edges[i][1]
                G.set_terminal_vertex(e, v)
                G.add_edge(v, vt, [f, ff])
                result_map[e] = result_map[e] * Word([f])
                result_map[ee] = Word([ff]) * result_map[ee]
                d[a[0]] = w[i + 1]
            else:
                vi = self._domain.initial_vertex(new_edges[i - 1][0])
                vt = self._domain.terminal_vertex(new_edges[i - 1][0])
                f = new_edges[i][0]
                # ee=A.inverse_letter(e) #already done
                ff = new_edges[i][1]
                self._domain.set_terminal_vertex(new_edges[i - 1][0], v)
                self._domain.add_edge(v, vt, [f, ff])
                result_map[e] = result_map[e] * Word([f])
                result_map[ee] = Word([ff]) * result_map[ee]
                d[a[0]] = w[i + 1]

        # updating self.edge_map after subdivision
        if A.is_positive_letter(e):
            d[e] = Word([self.image(e)[0]])
        else:
            d[ee] = Word([self.image(ee)[-1]])

        self.set_edge_map(d)

        return result_map

    def illegal_turns(self, turns=None):
        """
        List of illegal turns in the domain graph.

        A turn is illegal if it is mapped by ``self`` to a degenerate
        turn.

        INPUT:

        - ``turns`` -- a list of turns of the domain graph. Default is None
          meaning all the turns of the graph. I not ``None`` return the
          sublist of ``turns`` consisting of illegal turns.


        EXAMPLES::

            sage: A = AlphabetWithInverses(2)
            sage: G = GraphWithInverses.rose_graph(A)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->aba,b->ab")
            sage: f.illegal_turns()
            [('a', 'b')]
        """
        result = []

        if turns is None:
            turns = self.domain().turns()

        for turn in turns:
            u = self.image(turn[0])
            v = self.image(turn[1])
            if len(u) == 0 or len(v) == 0 or u[0] == v[0]:
                result.append(turn)
        return result

    def stallings_folding(self):
        """
        Implement Stallings' folding to get an immersion from ``self``.

        The domain of ``self`` is fold until we get an
        immersion. Intended to be used to compute the pullback of two
        graph maps and the intersection of subgroupes of a free group.

        ALGORITHM:

        We first subdivide edges of the domain according to length of
        their image.

        Then fold one gate at one vertex and update the edge map and
        illegal turns list.

        Repeat the process till no illegal turns remain.

        EXAMPLES::

            sage: A = AlphabetWithInverses(2)
            sage: G = GraphWithInverses.rose_graph(A)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->aba,b->ab")
            sage: f.stallings_folding()
            sage: print f
            Graph map:
            a: 1->1, c: 1->1
            a: 0->0, b: 0->0
            edge map: a->a, c->b

        REFERENCES:

            [Stallings] J. Stallings, Topology of Finite Graphs,

        AUTHOR:

            - Radhika GUPTA

        """
        A = self.domain().alphabet()
        for a in A:
            if len(self.image(a)) > 1:
                self.subdivide_domain(a)

        Turns = self._domain.turns()
        # list of all turns in domain after subdivision
        Il_turns = self.illegal_turns(Turns)
        # list of illegal turns in domain after subdivision
        counter = 0
        while len(Il_turns) > 0:
            counter = counter + 1

            # find edge_list (list of edges in the gate correspoding to e1)
            # to fold at exactly one vertex
            e1 = Il_turns[0][0]
            edge_list = [e1]
            for a in A:
                if self._domain.initial_vertex(a) == \
                        self._domain.initial_vertex(e1) and e1 != a:
                    if (e1, a) in Il_turns or (a, e1) in Il_turns:
                        edge_list.append(a)

            edge_list = list(set(edge_list))  # remove duplicates
            # fold at initial_vertex of e1 ( this function updates the
            # domain and edge_map)
            self._domain.fold(edge_list, [])

            # update edge_map again
            d = {}
            d[edge_list[0]] = self.image(edge_list[0])
            for a in A:
                if a not in edge_list:
                    d[a] = self.image(a)
            wm = WordMorphism(d)
            self.set_edge_map(wm)
            Turns = self._domain.turns()  # update list of all turns in domain
            Il_turns = self.illegal_turns(Turns)
            # update list of illegal turns in domain

    def pullback(self, other):
        r"""
        Pullback of the graph maps ``self`` and ``other``.
        The codomain of ``self`` and ``other`` must be the same graph.

        The pullback is a graph map f:G3 -> G that makes the diagram commute:

            G3 -----> G1
            |  \      |
            |   \     | self
            |    \f   |
            |     \   |
            V     _\| V
            G2 -----> G
            ....other

        The pullback method can be used to find intersection of two subgroups
        of a Free Group.

        INPUT: 

        - ``other`` -- a graph map G2->G with ``self``: a graph map G1->G,

        OUTPUT: 
        
        A ``GraphMap`` f

        EXAMPLES::
  
            sage: G1 = GraphWithInverses.rose_graph(AlphabetWithInverses(2,type='x0'))
            sage: G2 = GraphWithInverses.rose_graph(AlphabetWithInverses(2,type='a0'))
            sage: G =  GraphWithInverses.rose_graph(AlphabetWithInverses(2))
            sage: n1 = WordMorphism({'x0':['a','a'],'x1':['b','a']})
            sage: n2 = WordMorphism({'a0':['b','a'],'a1':['b','b','b','a','B','a']})
            sage: f1 = GraphMap(G1,G,n1)
            sage: f2 = GraphMap(G2,G,n2)
            sage: print f1.pullback(f2)
            Graph map:
            a0: (0, 0)->(1, 2), a1: (0, 2)->(1, 0), a2: (0, 2)->(1, 3), a3: (0, 3)->(1, 4), a4: (0, 4)->(1, 3), a5: (1, 2)->(0, 0), a6: (1, 4)->(0, 3)
            a: 0->0, b: 0->0
            edge map: a0->b, a1->a, a2->b, a3->b, a4->a, a5->a, a6->a

        AUTHORS:

            - Radhika GUPTA
        """
        import itertools
        # First convert self and f2 into immersions
        self.stallings_folding()
        other.stallings_folding()

        G3 = GraphWithInverses()
        A = AlphabetWithInverses(0, type='a0')
        d = {}
        # get set of vertices
        V = []
        for i in itertools.product(self.domain().vertices(),
                                   other.domain().vertices()):
            V.append(i)

        # add edges
        for v in V:
            for w in V:
                for e1 in self.domain().alphabet().positive_letters():
                    if self.domain().initial_vertex(e1) == v[0] \
                            and self.domain().terminal_vertex(e1) == w[0]:
                        for e2 in other.domain().alphabet().positive_letters():
                            if other.domain().initial_vertex(e2) == v[1] \
                                    and other.domain().terminal_vertex(e2) == w[
                                        1]:
                                if self.image(e1) == other.image(e2):
                                    e = A.add_new_letter()
                                    G3.add_edge(v, w, e)
                                    # update dictionary to define map on G3
                                    d[e[0]] = self.image(e1)

        G3._alphabet = A
        n3 = WordMorphism(d)
        G = self.codomain()  # same as other.codomain()

        return GraphMap(G3, G, n3)

    @staticmethod
    def rose_map(automorphism):
        """
        The graph map of the rose representing the automorphism.

        The rose is built on a copy of the alphabet of the domain of
        ``automorphism``.

        OUTPUT:

        The graph map of the rose representing the automorphism.

        EXAMPLES::

            sage: phi=FreeGroupAutomorphism('a->ab,b->ac,c->a')
            sage: print GraphMap.rose_map(phi)
            Graph map:
            a: 0->0, b: 0->0, c: 0->0
            a: 0->0, b: 0->0, c: 0->0
            edge map: a->ab, b->ac, c->a
        """

        A = AlphabetWithInverses(automorphism.domain().variable_names())
        graph = GraphWithInverses.rose_graph(A)
        return GraphMap(
            graph, graph,
            automorphism.to_word_morphism(
                use_str=True, upper_case_as_inverse=True))
