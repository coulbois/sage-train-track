r"""
MarkedGraph and MarkedMetricGraph

marked_graph module, defines Class for MarkedGraph and MarkedMetricGraph

AUTHORS:

- Thierry COULBOIS (2013-01-01): initial version
- Dominique BENIELLI (2016-02_15):
  AMU University <dominique.benielli@univ-amu.fr>, Integration in SageMath

EXAMPLES::

    sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
    sage: from sage.groups.free_groups.marked_graph import MarkedGraph
    sage: G = GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
    sage: print(MarkedGraph(G))
    Marked graph: a: 0->0, c: 1->0, b: 0->1
    Marking: a->a, b->bc
"""

# *****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# *****************************************************************************

from __future__ import print_function, absolute_import
from .inverse_graph import GraphWithInverses, MetricGraph
from .graph_map import GraphMap
from sage.combinat.words.morphism import WordMorphism
from .inverse_alphabet import AlphabetWithInverses
from sage.combinat.words.word import Word


class MarkedGraph(GraphWithInverses):
    """
    A ``MarkedGraph`` is a ``GraphWithInverses`` together with a marking.

    A marking is a homotopy equivalence (here a ``GraphMap``)
    from the rose to the graph.

    A ``MarkedGraph`` can be created from a ``GraphWithInverses`` by
    computing (randomly) a rose equivalent to the graph.

    EXAMPLES::

        sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
        sage: from sage.groups.free_groups.marked_graph import MarkedGraph
        sage: G = GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
        sage: print(MarkedGraph(G))
        Marked graph: a: 0->0, c: 1->0, b: 0->1
        Marking: a->a, b->bc

    AUTHORS:

    - Thierry Coulbois (2013-05-16)
    """

    def __init__(self, graph=None, marking=None, alphabet=None,
                 marking_alphabet=None):
        """
        INPUT:

        - ``graph`` -- (default None) GraphWithInverses is expected
          or will be combute from ''grap''
        - ``marking`` -- (default None) GraphMap is expected
          or will be compute
        - ``alphabet`` -- (default None) if ``graph`` is GraphWithInverses
          ``alphabet`` will be use for ``self``
        - ``marking_alphabet`` -- (default None) alphabet used in the case of a
          ``MarkedGraph`` is created from a GraphWithInverses`` by
          computing (randomly) a rose equivalent to the graph.

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph
            sage: from sage.groups.free_groups.graph_map import GraphMap
            sage: G = GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
            sage: M = MarkedGraph(graph=G)
            sage: print(M)
            Marked graph: a: 0->0, c: 1->0, b: 0->1
            Marking: a->a, b->bc
            sage: A = AlphabetWithInverses(2)
            sage: G = GraphWithInverses.rose_graph(A)
            sage: H = GraphWithInverses.rose_graph(A)
            sage: f = GraphMap(G,H,"a->aba,b->ab")
            sage: M = MarkedGraph(marking=f)
            sage: print(M)
            Marked graph: a: 0->0, b: 0->0
            Marking: a->aba, b->ab
            sage: print(MarkedGraph(marking=f, alphabet=A))
            Marked graph: a: 0->0, b: 0->0
            Marking: a->aba, b->ab
            sage: print(MarkedGraph(marking=f, marking_alphabet=A))
            Marked graph: a: 0->0, b: 0->0
            Marking: a->aba, b->ab
        """
        if isinstance(marking, GraphMap):
            GraphWithInverses.__init__(self,
                                       marking.codomain(),
                                       marking.codomain().alphabet())
            self._marking = marking
        else:
            if isinstance(graph, GraphWithInverses):
                alphabet = graph.alphabet()
            GraphWithInverses.__init__(self, graph, alphabet)

            if marking is None:  # computes a (random) marking
                # from a rose equivalent to graph

                A = graph.alphabet()
                tree = graph.spanning_tree()

                j = 0
                letter = dict()
                for a in A.positive_letters():
                    vi = graph.initial_vertex(a)
                    vt = graph.terminal_vertex(a)
                    if (len(tree[vi]) == 0 or
                            tree[vi][-1] != A.inverse_letter(a)) \
                            and (len(tree[vt]) == 0 or tree[vt][-1] != a):
                        letter[j] = a
                        j = j + 1

                B = AlphabetWithInverses(j)
                RB = GraphWithInverses.rose_graph(B)

                edge_map = dict()

                for i in range(j):
                    a = letter[i]
                    edge_map[B[i]] = graph.reduce_path(
                        tree[graph.initial_vertex(a)] * Word([a]) *
                        graph.reverse_path(tree[graph.terminal_vertex(a)]))
                marking = GraphMap(RB, graph, edge_map)
            else:
                marking = GraphMap(
                    GraphWithInverses.rose_graph(marking_alphabet),
                    self, marking)
            self._marking = marking

    def __str__(self):
        """
        String representation of ``self``.

        OUTPUT:

        String representation of ``self``.

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph
            sage: G=GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
            sage: print(MarkedGraph(G))
            Marked graph: a: 0->0, c: 1->0, b: 0->1
            Marking: a->a, b->bc
            sage: MarkedGraph(G).__str__()
            'Marked graph: a: 0->0, c: 1->0, b: 0->1\nMarking: a->a, b->bc'
        """
        result = "Marked graph: "
        for a in self._alphabet.positive_letters():
            result = result + a + ": {0}->{1}, ".format(
                self.initial_vertex(a), self.terminal_vertex(a))
        result = result[:-2] + "\n"
        result += "Marking: "
        for a in self._marking._domain._alphabet.positive_letters():
            result += a + "->" + self._marking.image(a).__str__() + ", "
        result = result[:-2]

        return result

    def marking(self):
        """
        A ``GraphMap`` from the rose to ``self``.

        OUTPUT:

        A ``GraphMap`` from the rose to ``self`` or ``marking`` input

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph
            sage: G=GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
            sage: G=MarkedGraph(G)
            sage: print(G.marking())
            Graph map:
            a: 0->0, b: 0->0
            a: 0->0, c: 1->0, b: 0->1
            edge map: a->a, b->bc
        """
        return self._marking

    def precompose(self, automorphism):
        """
        Precompose the marking by ``automorphism``.

        INPUT:

        - ``automorphism``: an automorphism of the free group on the
          rose that marks ``self``.

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph
            sage: G=GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
            sage: G=MarkedGraph(G)
            sage: phi=FreeGroupAutomorphism("a->aba,b->ab")
            sage: print(G.precompose(phi))
            Marked graph: a: 0->0, c: 1->0, b: 0->1
            Marking: a->abca, b->abc
        """
        edge_map = dict()
        for a in self._marking.domain().alphabet().positive_letters():
            edge_map[a] = self._marking(
                automorphism.to_word_morphism(
                    use_str=True, upper_case_as_inverse=True).image(a))
        self._marking.set_edge_map(edge_map)
        return self

    def difference_of_marking(self, other):
        """
        A ``GraphMap`` from ``self`` to ``other`` that makes
        the markings commute.

        INPUT:

        - ``other`` -- a MarkedGraph

        OUTPUT:

        Marking differences

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph
            sage: G=GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
            sage: G=MarkedGraph(G)
            sage: H=GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: H=MarkedGraph(H)
            sage: print(G.difference_of_marking(H))
            Graph map:
            a: 0->0, c: 1->0, b: 0->1
            a: 0->0, b: 0->1, c: 1->1
            edge map: a->a, c->, b->bcB
        """

        return other.marking() * self.marking().inverse()

    def subdivide(self, edge_list):
        """
        Subdivides each edge in the edge_list into two edges.

        INPUT:

        - ``edge_list`` -- edge list

        OUTPUT:

        Subdivide map from subdivide GraphWithInverses.

        .. WARNING:

            Each edge in ``edge_list`` must appear only once.

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph
            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: G = MarkedGraph(G)
            sage: G.subdivide(['a','c'])
            {'A': word: DA,
             'B': word: B,
             'C': word: EC,
             'a': word: ad,
             'b': word: b,
             'c': word: ce}
            sage: print(G)
            Marked graph: a: 0->2, b: 0->1, c: 1->3, d: 2->0, e: 3->1
            Marking: a->ad, b->bceB

        .. SEEALSO::

            :meth:`sage.groups.free_groups.inverse_graph.GraphWithInverses.subdivide()`
        """

        subdivide_map = GraphWithInverses.subdivide(self, edge_list)
        subdivide_morph = WordMorphism(subdivide_map)
        self._marking.set_edge_map(subdivide_morph * self._marking._edge_map)
        return subdivide_map

    def fold(self, edges_full, edges_partial):
        """
        Folds the list of edges.

        Some edges are fully folded and some are only partially
        folded. All edges are assumed to start form the same vertex.
        Edges are given by their label. In the terminology of
        Stallings folds the partially fold edges are subdivided and
        then fold.

        The first element of ``edges_full`` is allowed to be a tuple
        ``(path,'path')`` and not an ``edge_label``. Then the other
        edges will be folded to the whole ``path``. In Stallings
        terminology, this is a sequence of folds of the successive
        edges of ``path``.

        INPUT:

        - ``edges_full``, are list of edges
        - ``edges_partial`` are list of edges (each
          possibly empty, but the union must have at least two edges).


        OUTPUT:

        A dictionary that maps old edges to new graph paths.

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph
            sage: G = GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,1,'c']])
            sage: G = MarkedGraph(G)
            sage: G.fold(['b'],['a'])
            {'A': word: AB,
             'B': word: B,
             'C': word: C,
             'a': word: ba,
             'b': word: b,
             'c': word: c}
            sage: print(G)
            Marked graph: a: 1->0, b: 0->1, c: 1->1
            Marking: a->ba, b->bcB

        .. SEEALSO::

            :meth:`sage.groups.free_groups.inverse_graph.GraphWithInverses.fold()``
        """

        fold_map = GraphWithInverses.fold(self, edges_full, edges_partial)
        fold_morph = WordMorphism(fold_map)
        self._marking.set_edge_map(fold_morph * self._marking._edge_map)
        return fold_map

    def contract_forest(self, forest):
        """
        Contract the forest.

        Each tree of the forest is contracted to the initial vertex
        of its first edge.

        INPUT:

        - ``forest`` is a list of disjoint subtrees each given as
          lists of edges.

        OUTPUT:

        A dictionary that maps old edges to new edges.


        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph
            sage: G = MarkedGraph.rose_marked_graph(AlphabetWithInverses(2))
            sage: G.contract_forest([['b']])
            {'A': word: A, 'B': word: , 'a': word: a, 'b': word: }

        .. SEEALSO::

            :meth:`sage.groups.free_groups.inverse_graph.GraphWithInverses.contract_forest()``
        """

        contract_map = GraphWithInverses.contract_forest(self, forest)
        contract_morph = WordMorphism(contract_map)
        self._marking.set_edge_map(contract_morph * self._marking._edge_map)
        return contract_map

    def blow_up_vertices(self, germ_components):
        """Blow-up ``self`` according to classes of germs given in
        ``germ_components``.

        INPUT:

        - ``germ_components`` a list of classes of germs outgoing from a
          vertex.

        OUTPUT:

        A dictionary that maps an old edge to the path in the new
        graph.

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph
            sage: G = MarkedGraph.rose_marked_graph(AlphabetWithInverses(2))
            sage: G.blow_up_vertices([['a','A'],['b'],['B']])
            {'A': word: cAC, 'B': word: eBD, 'a': word: caC, 'b': word: dbE}
            sage: print(G)
            Marked graph: a: 1->1, b: 2->3, c: 0->1, d: 0->2, e: 0->3
            Marking: a->caC, b->dbE
        """
        blow_up_map = GraphWithInverses.blow_up_vertices(self, germ_components)
        blow_up_morph = WordMorphism(blow_up_map)
        self._marking.set_edge_map(blow_up_morph * self.marking().edge_map())
        return blow_up_map

    @staticmethod
    def rose_marked_graph(alphabet):
        """
        The rose on ``alphabet`` marked with the identity.

        INPUT:

        - ``alphabet`` -- an alphabet

        OUTPUT:

        The rose on ``alphabet`` marked with the identity.

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph
            sage: print(MarkedGraph.rose_marked_graph(AlphabetWithInverses(2)))
            Marked graph: a: 0->0, b: 0->0
            Marking: a->a, b->b
        """

        marking = dict((a, Word([a])) for a in alphabet.positive_letters())
        return MarkedGraph(graph=GraphWithInverses.rose_graph(alphabet),
                           marking=marking, marking_alphabet=alphabet)


class MarkedMetricGraph(MarkedGraph, MetricGraph):
    """
    A ``MarkedGraph`` together with a length function on edges.

    This is intended to represent point un outer space. Moreover,
    length may be set to 0 to represent simplicial trees in the
    boundary of outer space.

    EXAMPLES::

        sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
        sage: from sage.groups.free_groups.marked_graph import MarkedGraph, MarkedMetricGraph
        sage: G = GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
        sage: G = MarkedGraph(G)
        sage: G = MarkedMetricGraph(G)
        sage: print(G)
        Marked graph: a: 0->0, c: 1->0, b: 0->1
        Marking: a->a, b->bc
        Length: a:1, c:1, b:1
    """

    def __init__(self, graph=None, marking=None, length=None, alphabet=None,
                 marking_alphabet=None):
        """
        Initialize ``self``.

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph, MarkedMetricGraph
            sage: G = GraphWithInverses({'a':(0,1),'b':(1,1),'c':(1,0)})
            sage: G = MarkedGraph(G)
            sage: G = MarkedMetricGraph(G)
            sage: print(G)
            Marked graph: a: 0->1, c: 1->0, b: 1->1
            Marking: a->ac, b->abA
            Length: a:1, c:1, b:1

        """

        MarkedGraph.__init__(self, graph=graph,
                             marking=marking,
                             alphabet=alphabet,
                             marking_alphabet=marking_alphabet)

        if length is None:
            length = dict((a, 1) for a in self.alphabet())
        else:
            for a in length.keys():
                length[self.alphabet().inverse_letter(a)] = length[a]

        self._length = length

    def __str__(self):
        """
        String representation for ``self``.

        OUTPUT:

        A string representation of ``self``

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph, MarkedMetricGraph
            sage: G = GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
            sage: G = MarkedGraph(G)
            sage: G = MarkedMetricGraph(G)
            sage: G.__str__()
            'Marked graph: a: 0->0, c: 1->0, b: 0->1\nMarking: a->a, b->bc\nLength: a:1, c:1, b:1'
        """
        result = MarkedGraph.__str__(self) + "\n"
        result += "Length: "
        for a in self.alphabet().positive_letters():
            result += a + ":{0}".format(self.length(a)) + ", "
        result = result[:-2]
        return result

    def length(self, a):
        """
        The length of the edge labeled by ``a``.

        INPUT:

        - ``a`` -- a letter of the alphabet

        OUTPUT:

        The length of the edge labeled by ``a``

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph, MarkedMetricGraph
            sage: G = GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
            sage: G = MarkedGraph(G)
            sage: G = MarkedMetricGraph(G)
            sage: G.length('a')
            1
        """
        return self._length[a]

    def set_length(self, a, l):
        """
        Set the length of the edge ``a`` to ``l``.

        INPUT:

        - ``a`` -- label of edge
        - ``l`` -- length associated

        EXAMPLES::

            sage: from sage.groups.free_groups.inverse_graph import GraphWithInverses
            sage: from sage.groups.free_groups.marked_graph import MarkedGraph, MarkedMetricGraph
            sage: G = GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
            sage: G = MarkedGraph(G)
            sage: G = MarkedMetricGraph(G)
            sage: G.set_length('a', 2)
            sage: G.length('a')
            2
        """
        self._length[a] = l
        self._length[self.alphabet().inverse_letter(a)] = l

    @staticmethod
    def splitting(i, A):
        """
        The ``MarkedMetricGraph`` that corresponds to the splitting
        ``F(A)=F(A[:i])*F(A[i:])``.

        This is a graph with two vertices linked by an edge e and a
        loop for each letter in A. Letters in A[:i] are attached to
        the first vertex while letters in A[:i] are attached to the
        second vertex.

        All loops have length 0, the splitting edge ``e`` has length 1.

        INPUT:

        - ``i`` -- integer correspond to the splitting index
        - ``A`` -- an alphabet

        OUTPUT:

        The ``MarkedMetricGraph`` corresponding to splitting.

        EXAMPLES::

            sage: from sage.groups.free_groups.marked_graph import  MarkedMetricGraph
            sage: A = AlphabetWithInverses(5)
            sage: print(MarkedMetricGraph.splitting(2,A))
            Marked graph: a: 0->0, b: 0->0, c: 1->1, d: 1->1, e:
            1->1, f: 0->1
            Marking: a->a, b->b, c->fcF, d->fdF, e->feF
            Length: a:0, b:0, c:0, d:0, e:0, f:1
        """

        graph = dict()
        length = dict()
        marking = dict()

        B = A.copy()
        [e, ee] = B.add_new_letter()

        for j in range(i):
            a = A[j]
            graph[a] = (0, 0)
            length[a] = 0
            marking[a] = Word([a])

        for j in range(i, len(A)):
            a = A[j]
            graph[a] = (1, 1)
            length[a] = 0
            marking[a] = Word([e, a, ee])

        graph[e] = (0, 1)
        length[e] = 1

        return MarkedMetricGraph(graph, marking, length, B, A)

    @staticmethod
    def HNN_splitting(A):
        """
        The marked metric graph corresponding to the HNN splitting
        F_N=F_{N-1}*<t>.

        This is rose marked graph with all edges of length 0 except ``A[0]``
        which is of length 1.

        INPUT:

        - ``A`` -- an alphabet

        OUTPUT:

        The marked metric graph corresponding to the HNN splitting.

        EXAMPLES::

            sage: from sage.groups.free_groups.marked_graph import MarkedMetricGraph
            sage: A=AlphabetWithInverses(4)
            sage: print(MarkedMetricGraph.HNN_splitting(A))
            Marked graph: a: 0->0, b: 0->0, c: 0->0, d: 0->0
            Marking: a->a, b->b, c->c, d->d
            Length: a:1, b:0, c:0, d:0
        """

        length = {a: 0 for a in A.positive_letters()}
        length[A[0]] = 1

        RA = GraphWithInverses.rose_graph(A)
        RAA = GraphWithInverses.rose_graph(A)
        marking = GraphMap(RA, RAA, {a: Word([a]) for a in A.positive_letters()})

        return MarkedMetricGraph(marking=marking, length=length)

