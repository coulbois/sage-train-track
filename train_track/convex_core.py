"""
ConvexCore

convex_core.py defines ConvexCore class.

AUTHORS:

- Thierry COULBOIS (2013-01-01) : initial version
- Dominique BENIELLI (2016-02_15) :
  AMU University <dominique.benielli@univ-amu.fr>,
  Integration in SageMath.

EXAMPLES::

    sage: from train_track import *
    sage: from train_track.convex_core import ConvexCore
    sage: from train_track.marked_graph import MarkedGraph
    sage: from train_track.inverse_graph import GraphWithInverses
    sage: phi = FreeGroupAutomorphism("a->ab,b->ac,c->a")
    sage: C = ConvexCore(phi)
    sage: C.vertices()
    [0, 1]
    sage: A = AlphabetWithInverses(2)
    sage: G1 = MarkedGraph(GraphWithInverses.rose_graph(A))
    sage: G2 = MarkedGraph(GraphWithInverses.rose_graph(A))
    sage: C = ConvexCore(G1, G2)
    sage: C.vertices()
    [0]
"""
# *****************************************************************************
#       Copyright (C) 2013 Matt Clay and Thierry Coulbois
#       <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# *****************************************************************************
from __future__ import print_function, absolute_import
from sage.combinat.words.word import Word
from sage.graphs.graph import DiGraph
from .inverse_graph import GraphWithInverses
from .inverse_alphabet import AlphabetWithInverses
from .inverse_graph import MetricGraph
from .graph_map import GraphMap
from .free_group_automorphism import FreeGroupAutomorphism
import bisect


class ConvexCore():
    """Guirardel's convex core of two simplicial
    trees with an action of a free group.

    Let T1 and T2 be trees with actions of the free group FN. G1=T1/FN
    and G2=T2/FN are MarkedGraph.

    A ConvexCore is a CW-complex of dimension 2. 2-cells are
    squares. 1-cells are edges labeled by edges of G1 or G2. A square
    is of the form::

    ......e
    ...------>
    ..|.......|
    f.|.......|.f
    ..|.......|
    ..v.......v
    ...------>
    ......e

    where e is an edge of G1 and f an edge of G2. G0 and G1 based

    MetricGraph with edges of length 0 can be used for trees with a
    non-free action of FN.

    - ``ConvexCore(phi)``: where ``phi`` is an automorphism of the
      free group ``F``. The convex core of the Cayley tree ``TA`` of
      the free group ``F`` with respect to its alphabet ``A``, and of
      the tree ``TA.Phi``, where ``Phi`` is the outer class of
      ``phi``.

    - ``ConvexCore(G1,G2)``: where ``G1`` and ``G2`` are two marked
      graphs (or two marked metric graphs): The convex core of the
      universal covers ``T1`` and ``T2`` of ``G1`` and ``G2``
      respectively. Edges of length 0 are quotient out.

    - ``ConvexCore(f)``: where ``f`` is a homotopy equivalence between
      graphs ``G1`` and ``G2``: The convex core of the universal
      covers ``T1`` and ``T2`` of ``G1`` and ``G2``, with the
      fundamental group ``F`` of ``G1`` acting on ``G2`` through
      ``f``. Edges of length 0 are quotient out.

    .. WARNING::

        It is assumed that boths graphs ``G1`` and ``G2`` do not have vertices
        of valence 1 or 2.

        It may work with vertices of valence 2 in particular if there
        are no twice light squares.

    EXAMPLES::

        sage: from train_track import *
        sage: from train_track.convex_core import ConvexCore
        sage: phi = FreeGroupAutomorphism("a->ab,b->ac,c->a")
        sage: phi = phi*phi
        sage: C = ConvexCore(phi)
        sage: print(C.slice('c',0))
        Looped multi-digraph on 2 vertices

        sage: C.vertices()
        [0, 1, 2, 3]

        sage: C.squares()
        [[3, 0, 2, 1, 'c', 'a']]

        sage: C.twice_light_squares()
        [[1, 4, 0, 5, 'a', 'c']]

        sage: phi=FreeGroupAutomorphism("a->aC,b->c,c->ccB")
        sage: G0 = MarkedGraph(GraphWithInverses.valence_3(3))
        sage: G1 = MarkedGraph(GraphWithInverses.valence_3(3))
        sage: G1.precompose(phi)
        sage: C = ConvexCore(G0,G1)
        sage: print(C.isolated_edges())
        [[7, 9, ('c', 0)]]

    AUTHORS:

    - Matt Clay
    - Thierry Coulbois Modified by

    """

    def __init__(self, *args, **keywords):
        """
        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi = FreeGroupAutomorphism("a->ab,b->ac,c->a")
            sage: C = ConvexCore(phi)
            sage: print(C.volume())
            0

        """
        if 'verbose' in keywords:
            verbose = keywords['verbose']
        else:
            verbose = False
        if len(args) == 2:  # ConvexCore(G,H)
            G0 = args[0]
            G1 = args[1]
            #  phi= FreeGroupAutomorphism(G0.difference_of_marking(G1).tighten())
            #  f = phi.rose_representative()
            f = G0.difference_of_marking(G1)
            f.tighten()
            g = f.inverse()
        elif len(args) == 1:
            if isinstance(args[0], GraphMap):  # ConvexCore(f)
                f = args[0]
                G0 = f.domain()
                G1 = f.codomain()
                f = args[0]
                g = f.inverse()
            elif isinstance(args[0], FreeGroupAutomorphism):  # ConvexCore(phi)
                phi = args[0].simple_outer_representative()
                f = phi.rose_representative()
                G0 = f.domain()
                G1 = f.codomain()
                g = f.inverse()
        elif len(args) == 4:  # ConvexCore(G,H,f,g)
            (G0, G1, f, g) = args

        self._G0 = G0
        self._G1 = G1

        t1 = G1.spanning_tree(
            verbose=(verbose and verbose > 1 and verbose - 1))
        t0 = G0.spanning_tree(
            verbose=(verbose and verbose > 1 and verbose - 1))
        self._t0 = t0
        self._t1 = t1

        self._f01 = f  # WARNING: it is necessary that f maps the base
        # point of G0 to the base point of G1 and
        # conversely
        self._f10 = g

        # In the sequel t1 is G1.spanning_tree() with v1 as root
        # (similarly v0 is the root of G0.spanning_tree()). A vertex in
        # T0 is designated by a path w from v0. An edge in T0 is
        # designated by (w,a) where w is path from v0 to the initial
        # vertex of a. Note that wa need not be reduced.  A vertex v
        # in G1 designates the vertex at the end of the path t1(v)
        # from v0. A positive letter b in A1 with initial vertex v
        # designates the edge (t1(v),b) in T1 (again t1(v)b need not
        # be reduced).

        A0 = G0.alphabet()
        A1 = G1.alphabet()

        if verbose:
            print("Building signed ends")
        self._build_signed_ends(
            verbose=(verbose and verbose > 1 and (verbose - 1)))

        signed_ends = self._signed_ends

        heavy_squares = []  # A 2-cell is a triple (w,v,a,b) with a,b
        # positive letters of A0 and A1 and w a
        # reduced path in G0 from v0 to the initial
        # vertex of a. v is the initial vertex of b
        # in G1. The edge b stands for the edge
        # t1(b)b.

        isolated_edges = []  # Edges that are not boundaries of
        # two-cells stored as (w,v,(b,1)) with
        # w a path in G0 starting at v0 and b a
        # positive letter in A1 standing for an
        # edge in T1 as above. Again v is the
        # initial vertex of b in G1.

        existing_edges = dict(((a, 0), False) for a in A0.positive_letters())

        twice_light_squares = []  # a twice light square stored as
        # (w,v,a,b) where w is a path in G0
        # starting at v0 and ending at
        # u=G0.initial_vertex(a). a is a letter
        # in A0 (not necessarily positive). b
        # is a positive letter in A1 standing
        # for an edge between the vertices
        # v=G1.initial_vertex(b) and v.b in
        # T1 as above. The corners (w,v) and
        # (w.a,v.b) are in the convex core.


        # close the slices by convexity
        for b in A1.positive_letters():
            if verbose:
                print("Building the slice of", b)
            empty_slice = True
            if len(signed_ends[b]) > 0:
                signed_ends[b].sort()
                if verbose > 1:
                    print("Signed ends of ", b, ":", signed_ends[b])
                common = signed_ends[b][0][0]
            for (w, sign) in signed_ends[b]:
                common_len = G0.common_prefix_length(common, w)
                if common_len < len(common):
                    common = common[:common_len]
                    if common_len == 0:
                        break
            wp = common
            for (w, sign) in signed_ends[b]:
                start = G0.common_prefix_length(wp, w)
                if start == len(wp) and start > common_len:  
                    start -= 1
                wp = w
                for i in range(start, len(w) - 1): 
                    a = w[i]
                    empty_slice = False
                    if A0.is_positive_letter(a):
                        existing_edges[(a, 0)] = True
                        heavy_squares.append(
                            (w[:i], G1.initial_vertex(b), a, b))
                    else:
                        aa = A0.inverse_letter(a)
                        existing_edges[(aa, 0)] = True
                        heavy_squares.append(
                            (w[:i + 1], G1.initial_vertex(b), aa, b))
                    if verbose:
                        print("Heavy square", heavy_squares[-1])
            if empty_slice:  # we need to check wether we add an isolated edge
                if verbose:
                    print("The slice of", b,
                           "is empty, looking for an isolated edge")
                if len(signed_ends[b]) > 1:
                    # The signed-ends have all the same sign but at
                    # most one.  They all come out from the same
                    # vertex.  If the there exists one sign different
                    # from all the others, then this signed-end is the
                    # prefix of all the others and the alphabetic
                    # order puts it in signed_ends[b][0].
                    v0 =  G0.initial_vertex(signed_ends[b][1][0][-1])

                    # we need at least two edges out of v0 without signs
                    outgoing_from_origin = [a for a in A0 if
                                            G0.initial_vertex(a) == v0]
                    if len(signed_ends[b]) + 1 < len(outgoing_from_origin):
                        isolated_edges.append((
                            common, G1.initial_vertex(b), (b, 1)))  # common
                        # stands for its terminal vertex
                        if verbose:
                            print("Isolated edge", (common, G1.initial_vertex(b), (b, 1)))
                    else:  # len(signed_ends[b])+1==len(outgoing_from_origin)
                        if signed_ends[b][0][1] != signed_ends[b][1][1]: # not all signs equal
                            signed_outgoing_edges = [e[0][-1] for e in
                                                     signed_ends[b] if e[1] == signed_ends[b][1][1]]
                            signed_outgoing_edges.append(A0.inverse_letter(common[-1]))
                        else:
                            signed_outgoing_edges = [e[0][-1] for e in signed_ends[b]]
                        for a in outgoing_from_origin:   # we look for the
                            #  only edge outgoing from the origin without a sign
                            if a not in signed_outgoing_edges:
                                break

                        if signed_ends[b][1][1] == '-':
                            twice_light_squares.append((common,
                                                        G1.initial_vertex(b),
                                                        a, b))
                        else:
                            twice_light_squares.append((G0.reduce_path(common*Word([a])),
                                                            G1.initial_vertex(b),
                                                            A0.inverse_letter(a), b))
                                
                        if verbose:
                            print("Twice-light square",
                                  twice_light_squares[-1])

                        if A0.is_positive_letter(a):
                            existing_edges[(a, 0)] = True
                        else:
                            aa = A0.inverse_letter(a)
                            existing_edges[(aa, 0)] = True
                else:  # len(signed_ends[b]==1)
                    a = common[-1]
                    if signed_ends[b][0][1] == '+':
                        twice_light_squares.append(
                            (common[:-1], G1.initial_vertex(b), a, b))
                    else:
                        twice_light_squares.append(
                            (common, G1.initial_vertex(b), A0.inverse_letter(a), b))
                    if verbose:
                        print("Twice-light square",
                              twice_light_squares[-1])
                    if A0.is_positive_letter(a):
                        existing_edges[(a, 0)] = True
                    else:
                        aa = A0.inverse_letter(a)
                        existing_edges[(aa, 0)] = True


        # create the convex core as a square complex

        edges = set()
        vertices = set()

        # they are three kind of cells:
        # - squares: (w,v,a,b) where a and b are positive letters
        # - edges: (w,v,(a,0)) or (w,v,(b,1)) where a and b are
        #  positive letters
        # - vertices: (w,v)

        # where w is a path in G0 starting at v0, v is a vertex in G1
        # standing for the vertex of T1 at the end of t1(v), a is a
        # letter of A0 and b is a letter of A1.

        # Note that len(cell)-2 is its dimension

        for sq in heavy_squares:
            (e0, e1, e2, e3) = self.boundary(sq)
            edges.add(e0)
            edges.add(e1)
            # we orient the next two edges for them to be
            # labeled with a positive letter
            edges.add((e3[0], e2[1], e0[2]))  
            edges.add((e0[0], e0[1], e1[2]))
            

            # we now add the four corners of the square

            vertices.add((e0[0], e0[1]))
            vertices.add((e1[0], e1[1]))
            vertices.add((e2[0], e2[1]))
            vertices.add((e3[0], e3[1]))
            
        for e in isolated_edges:
            edges.add(e)
            vi, vt = self.boundary(e)
            vertices.update([vi, vt])

        for sq in twice_light_squares:
            vertices.add((sq[0],sq[1]))
            (e0, e1, e2, e3) = self.boundary(sq)
            vertices.add((e0[0], e0[1]))
            vertices.add((e2[0], e2[1])) 

            

        vertex_labels = list(vertices)
        vertex_labels.sort()

        if verbose:
            print("Vertices", vertex_labels)

        # There are still isolated edges of the form (a,0) missing
        for a in A0.positive_letters():
            if not existing_edges[(a, 0)]: 
                if verbose:
                    print("Looking for the isolated edge", (a, 0))

                aa = A0.inverse_letter(a)
                occurences = dict()

                done =  False
                i = 1
                while not done:
                    # we first look for the farthest occurence of a or aa in vertices
                    for (w,v) in vertices:
                        if len(w)>=i and (w[-i]==a or w[-i]==aa):
                            if v not in occurences or occurences[v][1] < len(w) - i:
                                occurences[v] = [(w,v),len(w)-i]

                    # we then check wether this occurence is part of the common prefix
                    for (w,v) in vertices:
                        if v in occurences and G0.common_prefix_length(w,occurences[v][0][0]) <= occurences[v][1]:
                            done = True
                            if occurences[v][0][0][occurences[v][1]] == a:
                                e = (occurences[v][0][0][:occurences[v][1]],v,(a,0))
                            else: # this was an occurence of the inverse letter
                                e = (occurences[v][0][0][:occurences[v][1]+1],v,(a,0))
                            edges.add(e)
                            isolated_edges.append(e)
                            if verbose:
                                print("Isolated edge:", e)
                            vi, vt = self.boundary(e)
                            vertices.update([vi, vt])
                            break
                    i+=1

        # We now number the vertices and change edges such that they
        #  are of the form [vi,vt,(a,side)]

        edges = list(edges)
        for i in range(len(edges)):
            e = edges[i]
            b = self.boundary(e)
            edges[i] = [bisect.bisect(vertex_labels, b[0]) - 1,
                        bisect.bisect(vertex_labels, b[1]) - 1, e[2]]

        # Do not forget the isolated edges

        for i, e in enumerate(isolated_edges):
            b = self.boundary(e)
            isolated_edges[i] = [bisect.bisect(vertex_labels, b[0]) - 1,
                                 bisect.bisect(vertex_labels, b[1]) - 1, e[2]]

        # We change the heavy squares such that they are
        # of the form [c1,c2,c3,c4,a,b]

        for i in range(len(heavy_squares)):
            sq = heavy_squares[i]
            b = self.boundary(sq)
            sq = [bisect.bisect(vertex_labels, (b[j][0], b[j][1])) - 1 for j in
                  range(4)] + [sq[2], sq[3]]
            heavy_squares[i] = sq

        # We change the twice_light_squares in the same fashion

        for i in range(len(twice_light_squares)):
            sq = twice_light_squares[i]
            b = self.boundary(sq)
            c0 = bisect.bisect(vertex_labels, (b[0][0], b[0][1])) - 1
            c2 = bisect.bisect(vertex_labels, (b[2][0], b[2][1])) - 1
            # The two next vertices are not
            #  part of the convex-core
            c1 = len(vertices) + 2 * i  
            c3 = len(vertices) + 2 * i + 1
            twice_light_squares[i] = [c0, c1, c2, c3, sq[2], sq[3]]

        # We now collapse squares and edges of length 0

        equivalent = range(len(vertices) + 2 * len(twice_light_squares))
        quotient = False
        if isinstance(G0, MetricGraph):
            i = 0
            while i < len(edges):
                [vi, vt, (a, side)] = edges[i]
                if side == 0 and G0.length(a) == 0:
                    quotient = True
                    vii = equivalent[vi]
                    while vi != vii:
                        vi = vii
                        vii = equivalent[vi]
                    vtt = equivalent[vt]
                    while vt != vtt:
                        vt = vtt
                        vtt = equivalent[vt]
                    if vi < vt:
                        equivalent[vt] = vi
                    else:
                        equivalent[vi] = vt
                    edges.pop(i)
                else:
                    i += 1
            i = 0
            while i < len(twice_light_squares):
                sq = twice_light_squares[i]
                if G0.length(sq[4]) == 0:
                    quotient = True
                    equivalent[sq[1]] = sq[0]
                    equivalent[sq[3]] = sq[2]
                    twice_light_squares.pop(i)
                    edges.append([sq[0], sq[2], (sq[5], 1)])
                else:
                    i += 1

            i = 0
            while i < len(heavy_squares):
                sq = heavy_squares[i]
                if G0.length(sq[4]) == 0:
                    quotient = True
                    heavy_squares.pop(i)
                else:
                    i += 1

            i = 0
            while i < len(isolated_edges):
                e = isolated_edges[i]
                if e[2][1] == 0 and G0.length(e[2][0]) == 0:
                    isolated_edges.pop(i)

        if isinstance(G1, MetricGraph):
            i = 0
            while i < len(edges):
                [vi, vt, (a, side)] = edges[i]
                if side == 1 and G1.length(a) == 0:
                    quotient = True
                    vii = equivalent[vi]
                    while vi != vii:
                        vi = vii
                        vii = equivalent[vi]
                    vtt = equivalent[vt]
                    while vt != vtt:
                        vt = vtt
                        vtt = equivalent[vt]

                    if vi < vt:
                        equivalent[vt] = vi
                    else:
                        equivalent[vi] = vt
                    edges.pop(i)
                else:
                    i += 1

            i = 0
            while i < len(twice_light_squares):
                sq = twice_light_squares[i]
                if G1.length(sq[5]) == 0:
                    quotient = True
                    equivalent[sq[3]] = sq[0]
                    equivalent[sq[1]] = sq[2]
                    twice_light_squares.pop(i)
                    if A0.is_positive_letter(sq[4]):
                        edges.append([sq[0], sq[2], (sq[4], 0)])
                    else:
                        edges.append(
                            [sq[2], sq[0], (A0.inverse_letter(sq[4]), 0)])
                else:
                    i += 1

            i = 0
            while i < len(heavy_squares):
                sq = heavy_squares[i]
                if G1.length(sq[5]) == 0:
                    heavy_squares.pop(i)
                else:
                    i += 1

            i = 0
            while i < len(isolated_eges):
                e = isolated_edges[i]
                if e[2][1] == 1 and G1.length(e[2][0]) == 0:
                    isolated_edges.pop(i)

        if quotient:
            for i in range(1, len(equivalent)):
                j = i
                k = equivalent[j]
                l = equivalent[k]
                while k > l:
                    equivalent[j] = l
                    j = k
                    k = l
                    l = equivalent[l]
                equivalent[i] = l

            vertices = [i for i in range(len(vertices)) if equivalent[i] == i]

            for e in edges:
                for i in range(2):
                    e[i] = equivalent[e[i]]

            for sq in heavy_squares:
                for i in range(4):
                    sq[i] = equivalent[sq[i]]

            for sq in twice_light_squares:
                for i in range(4):
                    sq[i] = equivalent[sq[i]]

        self._squares = heavy_squares
        self._edges = edges
        if quotient:
            self._vertices = vertices
        else:
            self._vertices = range(len(vertices))
        self._twice_light_squares = twice_light_squares
        self._vertex_labels = vertex_labels

        self._isolated_edges = isolated_edges

    def _build_signed_ends(self, consolidate=True, verbose=False):
        """
        For each edge of G1 computes a list of edges in T0 assigned with a
        + or a - sign.

        It is assumed that ``f=self._f01``: G0->G1 is

        - a continuous ``GraphMap``
        - a homotopy equivalence
        - that maps the root v0 of ``G0.spanning_tree()`` to the root v1 of
          ``G1.spanning_tree()``
        - the image of each vertex has at least two gates.

        Conversely ``g=self._f10``: G1->G0 is a continuous
        ``GraphMap`` that is a homotopy inverse of ``f`` and that maps
        v1 to v0.

        The universal cover of G0 and G1 are identified with paths in
        G0 and G1 based at v0 and v1. We choose the lifts of ``f`` and ``g``
        that maps v0 to v1 and conversely.

        Fix an edge e1 in T1. An edge e0 in T0 is assigned a + if its
        image f(e0) crosses e1 positively.

        TESTS::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi = FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C = ConvexCore(phi)
            sage: C._build_signed_ends()
            sage: print(C._signed_ends)
            {'a': [(word: Ca, '+'), (word: Cb, '+'), (word: a, '+'), (word: b, '+'), (word: c, '+')], 'c': [(word: Ba, '+')], 'b': [(word: Bca, '+'), (word: Bcb, '+'), (word: Bcc, '+')]}
        """

        G0 = self._G0
        G1 = self._G1

        f = self._f01
        g = self._f10

        A0 = G0.alphabet()
        A1 = G1.alphabet()

        t0 = self._t0
        t1 = self._t1

        # the positive letter b in A1 stands for the edge (t1(b),b) of
        # the universal cover of G1 (where t1(b) is the path in t1
        # from the root to the initial vertex of b). WARNING: with
        # this definition the edge b may not be oriented away from the
        # base point v1.

        signed_ends = dict((b, []) for b in A1.positive_letters())

        for a in A0.positive_letters():
            aa = A0.inverse_letter(a)
            image_a = f.image(a)
            w = t0[G0.initial_vertex(a)]
            w = G0.reduce_path(g(f(G0.reverse_path(w))) * w)
            for b in image_a:  # the image f(a) crosses the edge prefix.b
                pb = A1.to_positive_letter(b)
                u0 = g(t1[G1.initial_vertex(pb)])
                if b == pb:
                    w0 = G0.reduce_path(u0 * w)
                    if len(w0) == 0 or w0[-1] != A0.inverse_letter(a):
                        signed_ends[pb].append((w0 * Word([a]), '+'))
                    else:
                        signed_ends[pb].append((w0, '-'))
                w = G0.reduce_path(g.image(A1.inverse_letter(b)) * w)
                if b != pb:
                    w0 = G0.reduce_path(u0 * w)
                    if len(w0) == 0 or w0[-1] != A0.inverse_letter(a):
                        signed_ends[pb].append((w0 * Word([a]), '-'))
                    else:
                        signed_ends[pb].append((w0, '+'))

        if consolidate:
            # In the case where there might be vertices of valence 2
            # or vertices with only two gates, we need to consolidate
            # the signed-ends. That-is-to-say if a vertex has only +
            # ends out of it then these ends have to be pull back
            # towards the origin

            for b in A1.positive_letters():
                signed_ends[b].sort()
                if verbose:
                    print("slice of ",b,":",signed_ends[b])
                i = 0
                j = 1

                while i<len(signed_ends[b]):

                    while (i>0 and (len(signed_ends[b][i-1][0])
                                    == len(signed_ends[b][i][0]))
                           and (G0.common_prefix_length(signed_ends[b][i-1][0],
                                                        signed_ends[b][i][0])
                                == len(signed_ends[b][i][0]) - 1)):
                        i -= 1
                    while (j < len(signed_ends[b])
                           and len(signed_ends[b][i][0]) == len(signed_ends[b][j][0])
                           and (G0.common_prefix_length(signed_ends[b][i][0],
                                                        signed_ends[b][j][0])
                                == len(signed_ends[b][i][0]) - 1)):
                        j +=1
                    if j-i+1 == G0.degree(G0.initial_vertex(signed_ends[b][i][0][-1])):
                        if len(signed_ends[b][i][0])>1:
                            if verbose:
                                print("Shifting backward:",signed_ends[b][i:j],
                                      " -> ",end='')
                            signed_ends[b][i:j] = [(signed_ends[b][i][0][:-1],signed_ends[b][i][1])]
                            if verbose:
                                print(signed_ends[b][i])
                        elif j-i>1 or (
                                len(signed_end[b])>1 and signed_ends[b][i][0][0]!=signed_ends[b][1-i][0][0]):
                            # the signed ends are outgoing from the origin v0
                            # if v0 is valence 2 then we put the sign on the
                            # same direction as the other signs.
                            if verbose:
                                print("Shifting backward (through the origin):",signed_ends[b][i:j],
                                      " -> ",end='')
                            signed_outgoing_edges = [signed_ends[b][k][0][0] for k in range(i,j)]
                            v0 = G0.initial_vertex(signed_ends[b][i][0][0])
                            for a in A0:
                                if G0.initial_vertex(a) == v0 and a not in signed_outgoing_edges:
                                    break
                            # we respect the alphabetic order by putting the new letter at the beginning
                            if signed_ends[b][i][1] == '+':
                                signed_ends[b] = [(Word([a]),'-')]+signed_ends[b][:i]+signed_ends[b][j:]
                            else:
                                signed_ends[b] = [(Word([a]),'+')]+signed_ends[b][:i]+signed_ends[b][j:]
                            
                            if verbose:
                                 print(signed_ends[b][0])
                           
                    else:
                        i = j

                    j = i+1
                           

                # The above procedure keeps the alphabetic order. But we
                # still have to deal with signed ends of length 1 which
                # might be at the beginning and the end of the list.
                if len(signed_ends[b])>1:
                    i=0
                    j=len(signed_ends[b])-1
                    while i<len(signed_ends[b]) and len(signed_ends[b][i][0])==1:
                        i+=1
                    while j>i and len(signed_ends[b][j][0])==1:
                        j-=1
                    if i+len(signed_ends[b])-j==G0.degree(G0.initial_vertex(signed_ends[b][0][0][0])) and signed_ends[b][0][0][0]!=signed_ends[b][i][0][0] and  signed_ends[b][j][0][0]!=signed_ends[b][j+1][0][0]:
                        w = signed_ends[b][i][0][:1] 
                        if verbose:
                            print("Shifting backward (through the origin):",signed_ends[b][:i],
                                  signed_ends[b][j+1:]," -> ", end='')
                        if signed_ends[b][0][1] == '+':
                            signed_ends[b][0:i] = [(w,'-')]
                        else:
                            signed_ends[b][0:i] = [(w,'+')]
                        signed_ends[b][j+1:]=[]
                        if verbose:
                            print(signed_ends[b][0])

                # We now push the signs away from the origin. As
                # signed ends are sorted (except possibly for signed
                # ends of length 1), the shortest one has index 0.
                
                done = False
                while not done:
                    done = True
                    w = signed_ends[b][0][0]
                    l = len(w)
                    outgoing_indices=[]
                    outgoing_letters=[A0.inverse_letter(w[-1])]
                    for i in range(1,len(signed_ends[b])):
                        if G0.common_prefix_length(w,signed_ends[b][i][0]) < l:
                            break
                        elif len(signed_ends[b][i][0]) == l+1:
                            outgoing_indices.append(i)
                            outgoing_letters.append(signed_ends[b][i][0][-1])
                    else:
                        if len(outgoing_indices)+2 == G0.degree(G0.terminal_vertex(w[-1])):
                            v0 = G0.terminal_vertex(w[-1]) 
                            for a in A0:
                                if G0.initial_vertex(a)==v0 and a not in outgoing_letters:
                                    break
                            if len(outgoing_indices)>0 or len(signed_ends[b])>1:
                                if verbose:
                                    print("Shifting forward:",signed_ends[b][0],[signed_ends[b][i] for i in outgoing_indices],"->",end='')
                                signed_ends[b][0]=(G0.reduce_path(w*Word([a])),signed_ends[b][0][1])
                                for i in reversed(outgoing_indices):
                                    signed_ends[b].pop(i)
                                if verbose:
                                    print(signed_ends[b][0])
                                done = False
                                
                    
            
        self._signed_ends = signed_ends

    def boundary(self, cell):
        """
        The boundary of a cell is the list of vertices bounding it.

        A cell is a square, an edge or a vertex. Squares are bounded
        by four vertices, edges by two vertices.

        Cells are coded in two different ways, either tuples or lists.

        A d dimensional cell is a d+2 tuple:

        - d=2: squares: (w,v,a,b) where w is a path in G0 starting
          from v0 standing for the vertex of T0 at the end of w, v is
          a vertex in G1 standing for the vertex at the end of t1(v)
          in T1, a is a positive letter in A0 and b is a positive
          letter in A1
        - d=1: edges: (w,v,(a,0)) or (w,v,(b,1)) with w and v as
          above. Note that edges are oriented and that wa needs not be
          reduced.
        - d=0: vertices: (w,v) with w and v as above
        - The boundary of a square is a list [e0,e1,e2,e3] of edges such that
          e0=(w,v,(a,0)) and e2 are edges with a positive letter
          a, and e1=(w,v,(b,1)) and e3 are edges with b a
          positive letter.
        - The boundary of an edge it is the list [v0,v1] of the initial vertex
          v0=(w,v) followed by the terminal vertex.

        Whereas for lists:

        - squares: ``[v0,v1,v2,v3,a,b]`` where v0,v1,v2 and v3 are
          integers standing for vertices and a,b are positive letters
          labeling edges of G0 and G1 :

          .....a
          v3 -------> v2
          .^.........^
          .|.........|
          .|b........|b
          .|.........|
          .|.........|
          .|....a....|
          v0 ------->v1

        - edges : ``[v0,v1,(a,side)]`` where ``v0`` and ``v1`` are
          integers standing for vertices a is a label of the tree on
          ``side``.

        INPUT:

        - ``cell`` square, an edge or a vertex. Squares are bounded
          by four vertices, edges by two vertices.

        OUTPUT:

        The boundary of a cell is the list of vertices bounding it.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi = FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C = ConvexCore(phi)
            sage: C.boundary((Word('C'), 0, 'c', 'a')) # boundary of a square
            [(word: C, 0, ('c', 0)),
            (word: , 0, ('a', 1)),
            (word: Bc, 0, ('C', 0)),
            (word: B, 0, ('A', 1))]

            sage: C.boundary([3, 0, 2, 1, 'c', 'a']) # boundary of a square
            [[3, 0, ('c', 0)], [0, 2, ('a', 1)], [2, 1, ('C', 0)], [1, 3, ('A', 1)]]

            sage: C.boundary((Word('Bc'),0,('C',0))) # boundary of an edge
            [(word: Bc, 0), (word: B, 0)]

            sage: C.boundary([2,1,'C']) # boundary of an edge
            [2, 1]

        """
        if isinstance(cell, tuple):
            if len(cell) == 4:  # cell is a square
                w, v, a, b = cell
                ww, vv = self.boundary((w, v, (b, 1)))[1]
                aa = self._G0.alphabet().inverse_letter(a)
                bb = self._G1.alphabet().inverse_letter(b)
                return [(w, v, (a, 0)),
                        (self._G0.reduce_path(w * Word([a])), v, (b, 1)),
                        (self._G0.reduce_path(ww * Word([a])), vv, (aa, 0)),
                        (ww, vv, (bb, 1))]
            elif len(cell) == 3:  # cell is an edge
                (w, v, (a, i)) = cell
                if i == 0:
                    vv = v
                    ww = self._G0.reduce_path(w * Word([a]))
                else:  # i=1
                    G0 = self._G0
                    G1 = self._G1
                    t1 = self._t1
                    f10 = self._f10
                    vv = G1.terminal_vertex(a)
                    aa = G1.alphabet().inverse_letter(a)
                    ww = G0.reduce_path(
                        f10(t1[vv] * Word([aa]) * G1.reverse_path(t1[v])) * w)
                return [(w, v), (ww, vv)]
        else:  # the cell is a list of the form [v0,v1,v2,v3,v4,a,b]:
            # square or [v0,v1,(a,side)]: edge
            if len(cell) == 6:
                a = cell[4]
                b = cell[5]
                aa = self._G0.alphabet().inverse_letter(a)
                bb = self._G1.alphabet().inverse_letter(b)
                return [[cell[0],cell[1],(a,0)],[cell[1],cell[2],(b,1)],[cell[2],cell[3],(aa,0)],[cell[3],cell[0],(bb,1)]]
            else:
                return cell[:2]

    def path_from_origin(self, vertex, side, verbose=False):
        """
        Path from the origin of ``self`` to ``vertex`` on ``side``.

        Recall that on each side, each connected component of the
        1-skeleton of ``self`` is a tree. The origin is a vertex

        - (v0,w1) with v0 the origin of G0 and w1 a vertex of G1.

        or

        - (w0,v1) with w0 a path of the form t0[v] and v1 the origin
          of G1.


        INPUT:

        - ``vertex``: either a 2-tuple ``(w,v)``. where w is a path in
          G0 starting from v0 standing for the vertex of T0 at the end
          of w, v is a vertex in G1 standing for the vertex at the end
          of t1(v) in T1. Or either an integer standing for a vertex
          of ``self``.
        - ``side``: 0 or 1 standing for ``T0`` or ``T1``
        - ``verbose`` -- (default: False) for verbose option

        OUTPUT:

        Path from the origin of ``self`` to ``vertex`` on ``side``.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C=ConvexCore(phi)
            sage: C.path_from_origin(2,0)
            word: Bc
            sage: C.path_from_origin(2,1)
            word: a

            sage: C.path_from_origin(('Bc',0),0)
            'Bc'

            sage: C.path_from_origin(('Bc',0),1)
            word: a

        """
        if not isinstance(vertex, tuple):  # The vertex is an integer
            vertex = self._vertex_labels[vertex]

        if side == 0:
            return vertex[0]
        else:  # side==1
            w = vertex[0]
            if len(w) == 0:
                return self._t1[vertex[1]]
            else:
                t0 = self._t0
                G0 = self._G0
                G1 = self._G1
                t1 = self._t1
                f01 = self._f01
                return G1.reduce_path(
                    f01(t0[G0.terminal_vertex(w[-1])] *
                        G0.reverse_path(w)) *
                        t1[vertex[1]])

    def tree(self, side):
        """
        ``T0`` or ``T1`` (according to ``side``) where ``self`` is the
        convex core of the trees ``T0`` and ``T1``.

        INPUT:

        - ``side`` 0 or 1 standing for ``T0`` or ``T1``

        OUTPUT:

        ``T0`` or ``T1`` (according to ``side``) where ``self`` is the
        convex core of the trees ``T0`` and ``T1``.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C=ConvexCore(phi)
            sage: print(C.tree(0))
            Marked graph: a: 0->0, b: 0->0, c: 0->0
            Marking: a->a, b->b, c->c

        """

        if side == 0:
            return self._G0
        else:
            return self._G1

    def squares(self):
        """
        List of squares of ``self``.

        OUTPUT:

        List of squares of ``self``.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C=ConvexCore(phi)
            sage: C.squares()
            [[3, 0, 2, 1, 'c', 'a']]

        """

        return self._squares

    def twice_light_squares(self):
        """
        List of twice light squares of ``self``.

        OUTPUT:

        List of twice light squares of ``self``

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C=ConvexCore(phi)
            sage: C.twice_light_squares()
            [[1, 4, 0, 5, 'a', 'c']]
        """

        return self._twice_light_squares

    def edges(self):
        """
        List of edges of ``self``.

        This includes the isolated edges of ``self`` but not the edges
        of the twice-light squares.

        OUTPUT:

        List of edges of ``self``.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C=ConvexCore(phi)
            sage: C.edges()
             [[3, 1, ('a', 1)],
              [1, 0, ('b', 0)],
              [2, 3, ('b', 1)],
              [1, 2, ('c', 0)],
              [0, 2, ('a', 1)],
              [3, 0, ('c', 0)]]

        """

        return self._edges

    def vertices(self):
        """
        List of vertices of ``self``.

        .. WARNING:

        The two vertices of a twice-light square that do not belong to
        the core are not vertices of ``self``.

        OUTPUT:

        List of vertices of ``self``.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C=ConvexCore(phi)
            sage: C.vertices()
            [0, 1, 2, 3]

        """
        return self._vertices

    def isolated_edges(self):
        """
        List of isolated edges

        OUTPUT:

        List of isolated edges

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C=ConvexCore(phi)
            sage: C.isolated_edges()
            [[2, 3, ('b', 1)], [1, 0, ('b', 0)]]

        """

        return self._isolated_edges

    def slice(self, a, side):
        """
        Slice of ``self`` for the edge ``a`` of the given ``side``.

        The slice is the tree whose vertices are edges labeled by
        ``(a,side)`` and with edges the squares with one side
        corresponding to ``(a,side)``.

        INPUT:

        - ``a``
          If ``self`` is the core of the trees ``T0`` and ``T1`` and
          ``side==0`` then ``a`` is an edge of ``T0``. Conversely if
          ``side==1`` then ``a`` is an edge of ``T1``.
        - ``side`` 0 or 1 standing for ``T0`` or ``T1``

        OUTPUT:

        A ``DiGraph``, edges are labeled by the corresponding
        square of ``self``,vertices by the corresponding edge.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C=ConvexCore(phi)
            sage: print(C.slice('c',0))
            Looped multi-digraph on 2 vertices
        """

        G = DiGraph(loops=True, multiedges=True)
        for sq in self.squares():
            if sq[4 + side] == a:
                if side == 0:
                    G.add_edge(((sq[0], sq[1], (a, 0)),
                                (sq[3], sq[2], (a, side)), sq[5]))
                else:
                    G.add_edge(((sq[0], sq[3], (a, 1)), (sq[1], sq[2], (a, 1)),
                                sq[4]))
        if len(G) == 0:
            for e in self.isolated_edges():
                if e[2] == (a, side):
                    G.add_vertex((e[0], e[1], e[2]))
        return G

    def one_squeleton(self, side, augmented=False):
        """One squeleton of ``self`` on the ``side``

        INPUT:

        - ``side`` is 0 or 1, standing for ``T0`` or ``T1``
        - ``augmented`` -- (default: False) if ``True`` twice light
          edges bounded a twice light squares are considered as edges.

        OUTPUT:

        A ``DiGraph`` edges are labeled by letters of the alphabet and
        vertices are labeled by the vertices of ``self``.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C=ConvexCore(phi)
            sage: C.one_squeleton(0)
            Looped multi-digraph on 4 vertices

            sage: C.one_squeleton(0,augmented=True) # Looped multi-digraph on 5 vertices
            Looped multi-digraph on 5 vertices
        """

        G = self.tree(side)
        A = G.alphabet()
        result = DiGraph(loops=True, multiedges=True)

        for e in self.edges():
            if e[2][1] == side:
                result.add_edge((e[0], e[1], e[2][0]))

        if augmented:
            for sq in self.twice_light_squares():
                if side == 0:
                    a = sq[4]
                    if A.is_positive_letter(a):
                        result.add_edge((sq[0], sq[1], a))
                    else:
                        aa = A.inverse_letter(a)
                        result.add_edge((sq[1], sq[0], aa))
                else:
                    b = sq[5]  # it is assumed that b is a positive letter
                    result.add_edge((sq[1], sq[2], b))

        return result

    def volume(self):
        """
        Volume of ``self``.

        If the trees are not metric trees then this is the simplicial
        volume: the number of squares in the 2-squeleton.

        If the trees are metric trees, then this is the volume.

        OUTPUT:

        Volume of ``self``.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")**2
            sage: C=ConvexCore(phi)
            sage: C.volume()
            1
        """

        G0 = self.tree(0)
        G1 = self.tree(1)

        if isinstance(G0, MetricGraph) and isinstance(G1, MetricGraph):
            result = 0
            for sq in self.squares():
                result += G0.length(sq[4]) * G1.length(sq[5])
            return result
        elif isinstance(G0, MetricGraph):
            result = 0
            for sq in self.squares():
                result += G0.length(sq[4])
            return result
        elif isinstance(G1, MetricGraph):
            result = 0
            for sq in self.squares():
                result += G1.length(sq[5])
            return result
        else:
            return len(self.squares())

    def squares_of_the_boundary(self, verbose=False):
        """
        List of squares which are not surrounded by 4 squares.

        This is an important information, either to run the Rips
        machine or to recognize a surface (with boundary).

        INPUT:

        - ``verbose`` -- (default: False) for verbose option

        OUTPUT:

        A list of pairs (square,i) where square is a square and i is
        0,1,2 or 3 designating the edge of square which is not bounded
        by another square.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi = FreeGroupAutomorphism("a->abaababa,b->abaab")
            sage: C = ConvexCore(phi)
            sage: C.squares_of_the_boundary()
            [(2, 0), (4, 2), (8, 1), (1, 1), (5, 3), (6, 3), (0, 0), (3, 2)]
            sage: C.squares_of_the_boundary(verbose=True)
            [(2, 0), (4, 2), (8, 1), (1, 1), (5, 3), (6, 3), (0, 0), (3, 2)]

        """

        valence = dict(((e[0], e[1], e[2]), True) for e in self.edges())
        # valence[e]=True if the edge e has valence 0,
        # valence[e]=(i,j) if i is the unique square bounding e and e
        # is the j-th edge of i and False if there are at least two
        # squares bounding e.

        for i, sq in enumerate(self.squares()):
            if valence[(sq[0], sq[1], (sq[4], 0))] is True:
                valence[(sq[0], sq[1], (sq[4], 0))] = (i, 0)
            else:
                valence[(sq[0], sq[1], (sq[4], 0))] = False

            if valence[(sq[0], sq[3], (sq[5], 1))] is True:
                valence[(sq[0], sq[3], (sq[5], 1))] = (i, 3)
            else:
                valence[(sq[0], sq[3], (sq[5], 1))] = False

            if valence[(sq[1], sq[2], (sq[5], 1))] is True:
                valence[(sq[1], sq[2], (sq[5], 1))] = (i, 1)
            else:
                valence[(sq[1], sq[2], (sq[5], 1))] = False

            if valence[(sq[3], sq[2], (sq[4], 0))] is True:
                valence[(sq[3], sq[2], (sq[4], 0))] = (i, 2)
            else:
                valence[(sq[3], sq[2], (sq[4], 0))] = False

        boundary_squares = [s for e, s in iter(valence.items()) if
                            ((s is not True) and (s is not False))]

        return boundary_squares


    def squares_orientation(self, orientation=1, verbose=False):
        """
        Assuming that ``self`` is an orientable surface square-complex,
        chose a coherent orientation of the squares.  A coherent
        orientation is such that two squares sharing an edge are
        coherently oriented.  If there are more than one strongly
        connected component of squares then they get different
        numbers.  Intended to be used by
        ``ConvexCore.plot_ideal_curve_diagram()``.

        INPUT:

        - ``orientation`` (default: 1): the orientation of the first
          square of ``self``. It can be either 1 or -1.
        - ``verbose`` -- (default: False) for verbose option

        OUTPUT:

        A list of positive and negative numbers such that two adjacent
        squares are coherently oriented (same number).

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi = FreeGroupAutomorphism("a->abaababa,b->abaab")
            sage: C = ConvexCore(phi)
            sage: C.squares_orientation()
            [1, -1, -1, -1, 1, -1, -1, 1, -1]
            sage: C.squares_orientation(orientation=2)
            [2, -2, -2, -2, 2, -2, -2, 2, -2]

        """

        squares = self.squares()

        if len(squares) == 0:
            return []

        squares_orientation = [orientation] + \
                              [0 for i in range(1, len(squares))]

        todo = [0]  # oriented squares with not yet oriented neighboors

        oriented = 1  #number of oriented squares

        while oriented < len(squares):
            while len(todo) > 0 and oriented < len(squares):
                i = todo.pop()
                sqi = squares[i]
                for j in range(1, len(squares)):
                    if squares_orientation[j] == 0:
                        sqj = squares[j]
                        if sqi[4] == sqj[4] and (
                                    (sqi[0] == sqj[0] and sqi[1] == sqj[1]) or
                                    (sqi[3] == sqj[3] and sqi[2] == sqj[2])):
                            squares_orientation[j] = - squares_orientation[i]
                            todo.append(j)
                            oriented += 1
                        elif sqi[4] == sqj[4] and (
                                    (sqi[0] == sqj[3] and sqi[1] == sqj[2]) or
                                    (sqi[3] == sqj[0] and sqi[2] == sqj[1])):
                            squares_orientation[j]=squares_orientation[i]
                            todo.append(j)
                            oriented += 1
                        elif sqi[5] == sqj[5] and (
                                    (sqi[0] == sqj[0] and sqi[3] == sqj[3]) or
                                    (sqi[1] == sqj[1] and sqi[2] == sqj[2])):
                            squares_orientation[j] = - squares_orientation[i]
                            todo.append(j)
                            oriented += 1
                        elif sqi[5] == sqj[5] and (
                                    (sqi[0] == sqj[1] and sqi[3] == sqj[2]) or
                                    (sqi[1] == sqj[0] and sqi[2] == sqj[3])):
                            squares_orientation[j] = squares_orientation[i]
                            todo.append(j)
                            oriented += 1
            if oriented < len(squares):  # there is more than one
                # strongly connected component
                if verbose:
                    print("There is another strongly connected component")
                for i in range(1, len(squares)):
                    if squares_orientation[i] == 0:
                        break
                todo.append(i)
                if orientation > 0:
                    orientation += 1
                else:
                    orientation -= 1
                squares_orientation[i] = orientation
                oriented += 1

        return squares_orientation

    def surface_boundary(self, orientation=None, verbose=False):
        """
        List of edges in the boundary of the square complex.

        Attended to be used by
        :meth:`train_track.convex_core.ConvexCore.plot_ideal_curve_diagram()`.

        INPUT:

        - ``orientation`` (default: None): list of square  orientation
        - ``verbose`` -- (default: False) for verbose option

        OUTPUT:

        A list of triples (v,w,(a,i,j)) where v and w are vertices a
        is a letter of the alphabet of the side i and j is an
        orientation: it can be 0 meaning that the edge is oriented in
        this direction or a non-zero number specifying the orientation
        of the square bounding the edge.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: phi = FreeGroupAutomorphism("a->abaababa,b->abaab")
            sage: C = ConvexCore(phi)
            sage: C.surface_boundary()
            [(8, 0, ('b', 0, -1)),
             (0, 8, ('B', 0, 1)),
             (3, 2, ('a', 0, -1)),
             (2, 3, ('A', 0, 1)),
             (7, 8, ('b', 1, -1)),
             (8, 7, ('B', 1, 1)),
             (2, 7, ('a', 1, -1)),
             (7, 2, ('A', 1, 1)),
             (11, 1, ('a', 1, 1)),
             (1, 11, ('A', 1, -1)),
             (4, 11, ('b', 1, 1)),
             (11, 4, ('B', 1, -1)),
             (1, 0, ('a', 0, 1)),
             (0, 1, ('A', 0, -1)),
             (3, 4, ('b', 0, 1)),
             (4, 3, ('B', 0, -1))]
             sage: C.surface_boundary(verbose=True)
             [(8, 0, ('b', 0, -1)),
              (0, 8, ('B', 0, 1)),
              (3, 2, ('a', 0, -1)),
              (2, 3, ('A', 0, 1)),
              (7, 8, ('b', 1, -1)),
              (8, 7, ('B', 1, 1)),
              (2, 7, ('a', 1, -1)),
              (7, 2, ('A', 1, 1)),
              (11, 1, ('a', 1, 1)),
              (1, 11, ('A', 1, -1)),
              (4, 11, ('b', 1, 1)),
              (11, 4, ('B', 1, -1)),
              (1, 0, ('a', 0, 1)),
              (0, 1, ('A', 0, -1)),
              (3, 4, ('b', 0, 1)),
              (4, 3, ('B', 0, -1))]

        """

        if orientation is None:
            orientation = getattr(self, '_squares_orientation', None)

        if orientation is None:
            orientation = self.squares_orientation()

        squares = self.squares()

        boundary_squares = self.squares_of_the_boundary(
            verbose=verbose and verbose > 1 and verbose - 1)

        result = []

        for (i, j) in boundary_squares:
            sq = squares[i]
            if j == 0 or j == 1:
                result.append((sq[j], sq[(j + 1) % 4],
                               (sq[4 + (j % 2)], j % 2, orientation[i])))
                result.append((sq[(j + 1) % 4], sq[j], (
                    self.tree(side=j).alphabet().inverse_letter(
                        sq[4 + (j % 2)]), j % 2, -orientation[i])))
            else:
                result.append((sq[(j + 1) % 4], sq[j],
                               (sq[4 + (j % 2)], j % 2, -orientation[i])))
                result.append((sq[j], sq[(j + 1) % 4], (
                    self.tree(side=j - 2).alphabet().inverse_letter(
                        sq[4 + (j % 2)]), j % 2, orientation[i])))

        for e in self.isolated_edges():
            result.append((e[0], e[1], (e[2][0], e[2][1], 0)))
            result.append((e[1], e[0], (
                self.tree(side=e[2][1]).alphabet().inverse_letter(e[2][0]),
                e[2][1], 0)))

        for sq in self.twice_light_squares():
            result.append((sq[0], sq[1], (sq[4], 0, 0)))
            result.append((sq[1], sq[2], (sq[5], 1, 0)))
            result.append((sq[1], sq[0], (
                self.tree(side=0).alphabet().inverse_letter(sq[4]), 0, 0)))
            result.append((sq[2], sq[1], (
                self.tree(side=1).alphabet().inverse_letter(sq[5]), 1, 0)))

        return result

    def plot_ideal_curve_diagram(self, radius=1, orientation=1,
                                 cyclic_order_0=None, cyclic_order_1=None,
                                 verbose=False):
        """
        Plot the set of ideal curves on the surface S=S(g,1) of genus g
        with one puncture.

        The free group has rank N=2g, the trees T0 and T1 are roses
        transverse to a maximal set of ideal curves on S. The convex
        core is transverse to the two collections of curves: vertices
        are connected components of the complement of the union of the
        two sets of curves, edges are arcs separating two regions and
        squares are around intersections points of curves.

        For instance T0 can be set to be the rose with the trivial
        marking, while T1 is obtained from T0 by applying a mapping
        class (and not a general automorphism). The embedding of the
        mapping class group is that generated by the
        ``surface_dehn_twist()`` method of the ``FreeGroup`` class.

        The set of ideal curves of T0 is drawn as the boundary of a
        regular 2N-gone, and the set of ideal curves of T1 is drawn
        inside this 2N-gone.

        INPUT:

        - ``radius``: (default: 1) the radius of the regular 2N-gone
          which is the fondamental domain of the surface.
        - ``cyclic_order_0``: (default None) List of edges outgoing
          from the sole vertex of T0 ordered according to the embedding
          in the surface. A typical value in rank 4, compatible with
          the definition of ``FreeGroup.surface_dehn_twist()`` is :
          ['A','B','a','C','D','c','d','b']
        - ``cyclic_order_1``: (default: None) List of edges outgoing
          from the sole vertex of T1 ordered according to the embedding
          in the surface.
        - ``orientation`` -- (default: 1): list of square  orientation
        - ``verbose`` -- (default: False) for verbose option

        OUTPUT:

        the set of ideal curves on the surface S=S(g,1) of genus g
        with one puncture.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: F=FreeGroup('a,b,c,d')
            sage: phi=mul([FreeGroupAutomorphism.surface_dehn_twist(F,i) for i in [2,1,1,4]])
            sage: C=ConvexCore(phi)
            sage: C.plot_ideal_curve_diagram(cyclic_order_0=['A','B','a','C','D','c','d','b'])
            Graphics object consisting of 28 graphics primitives
            sage: C.plot_ideal_curve_diagram(cyclic_order_0=['A','B','a','C','D','c','d','b'], verbose=True)
            The tree on side 0 is embedded in the surface: ['A', 'B', 'a', 'C', 'D', 'c', 'd', 'b']
            ...
            Graphics object consisting of 28 graphics primitives
        """
        from sage.plot.graphics import Graphics
        from sage.plot.line import Line, line
        from sage.plot.text import text
        from sage.plot.arrow import Arrow
        from sage.rings.real_mpfr import RR
        from numpy import cos
        from numpy import sin
        from numpy import pi

        T0 = self.tree(0)
        T1 = self.tree(1)
        A0 = T0.alphabet()
        N = len(A0)
        A1 = T1.alphabet()

        # Let ``self`` be the convex core of trees T0 and T1. T0 and
        # T1 need to be roses. The trees T0 and T1 may be given as
        # embedded inside the surface. In this case the edges outgoing
        # from the sole vertex are cyclically ordered.

        if len(T0.vertices()) != 1:
            raise ValueError('The tree on side 0 must be a rose')
        if len(T1.vertices()) != 1:
            raise ValueError('The tree on side 1 must be a rose')

        if cyclic_order_0 is None:
            cyclic_order_0 = getattr(T0, 'cyclic_order', None)
        if cyclic_order_1 is None:
            cyclic_order_1 = getattr(T1, 'cyclic_order', None)

        if verbose:
            if cyclic_order_0 is not None:
                print("The tree on side 0 is embedded in the surface:",
                        cyclic_order_0)
            else:
                print("The tree on side 0 is not embedded in the surface,"
                       " we will try to guess an embedding")
            if cyclic_order_1 is not None:
                print("The tree on side 1 is embedded in the surface:",
                       cyclic_order_1)
            else:
                print("The tree on side 1 is not embedded in the surface, "
                       "we will try to guess an embedding")

        squares = self.squares()

        # Coherent orientation of the squares

        orientation = self.squares_orientation(
            orientation=orientation,
            verbose=verbose and verbose > 1 and verbose - 1)

        if verbose:
            print("Orientation of the squares:")
            if verbose > 1:
                for i, sq in enumerate(squares):
                    print(i, ":", sq, ":", orientation[i])

        boundary = self.surface_boundary(
            orientation=orientation,
            verbose=verbose and verbose > 1 and verbose - 1)

        if verbose:
            print("Edges of the boundary:")
            print(boundary)

        # The boundary of the surface is an Eulerian circuit in the
        #  surface_boundary_graph

        eulerian_circuits = []

        boundary_length = 2 * (
            self.tree(side=0).alphabet().cardinality() + self.tree(
                side=1).alphabet().cardinality())

        next = [(boundary[0], 0)]
        if boundary[0][2][2] != 0:
            next.append((boundary[1], 0))

        if verbose:
            print("Looking for an eulerian circuit in the boundary")

        while len(next) > 0:

            e, current = next.pop()

            if verbose:
                print(e, current)

            for i in range(current + 1, len(boundary)):
                if boundary[i] == e:
                    boundary[i], boundary[current] = \
                        boundary[current], boundary[i]
                    # now the boundary is the beginning of an eulerian
                    # circuit up to current
                    break

            # We check that the boundary up to current is acceptable

            acceptable = True

            # First, we check that two edges bounding a strongly
            # connected component of squares share the same
            # orientation

            oriented = set()
            for i in range(current + 1):
                e = boundary[i]
                if e[2][2] != 0 and -e[2][
                        2] in oriented:  # edges with orientation 0
                    # are isolated edges
                    acceptable = False
                    if verbose:
                        print("The current boundary does not respect" \
                              " orientation", e[2][2])
                    break
                else:
                    oriented.add(e[2][2])

            if not acceptable:
                continue

            # Next we check that this is compatible with the given
            # cyclic order

            if cyclic_order_0 is not None:
                i = 0
                j0 = None
                while i < current + 1 and boundary[i][2][1] != 0:
                    i += 1
                if i < current + 1:
                    j0 = 0
                    while j0 < len(cyclic_order_0) and cyclic_order_0[j0] != \
                            boundary[i][2][0]:
                        j0 += 1

                while i < current:
                    i += 1
                    while i < current + 1 and boundary[i][2][1] != 0:
                        i += 1
                    if i < current + 1:
                        j0 += 1
                        if j0 == len(cyclic_order_0):
                            j0 = 0
                        if boundary[i][2][0] != cyclic_order_0[j0]:
                            acceptable = False
                            if verbose:
                                print("The current boundary does not respect"
                                       " the given cyclic order on side 0")
                            break

            if not acceptable:
                continue

            if cyclic_order_1 is not None:
                i = 0
                j1 = None
                while i < current + 1 and boundary[i][2][1] != 1:
                    i += 1
                if i < current + 1:
                    j1 = 0
                    while j1 < len(cyclic_order_1) and cyclic_order_1[j1] != \
                            boundary[i][2][0]:
                        j1 += 1
                while i < current:
                    i += 1
                    while i < current + 1 and boundary[i][2][1] != 1:
                        i += 1
                    if i < current + 1:
                        j1 += 1
                        if j1 == len(cyclic_order_1):
                            j1 = 0
                        if boundary[i][2][0] != cyclic_order_1[j1]:
                            acceptable = False
                            if verbose:
                                print("The current boundary does not respect "
                                       "the given cyclic order on side 1")

                            break

            if not acceptable:
                continue

            # If there are no given cyclic orders we check that on
            # both side there is only one connected component.

            if (cyclic_order_0 is None) and (cyclic_order_1 is None):
                tmp_cyclic_0 = [boundary[i][2][0] for i in range(current + 1)
                                if boundary[i][2][1] == 0]
                i = 0
                if len(tmp_cyclic_0) < 2 * len(A0):
                    while i < len(tmp_cyclic_0):
                        j = i
                        done = False
                        while True:
                            aa = A0.inverse_letter(tmp_cyclic_0[j])
                            j = 0
                            while j < len(tmp_cyclic_0) and tmp_cyclic_0[
                                  j] != aa:
                                j += 1
                            if j == len(tmp_cyclic_0) or j == 0:
                                i += 1
                                break
                            j -= 1
                            if i == j:
                                acceptable = False
                                if verbose:
                                    print("There is more than one boundary "
                                           "component on side 0")
                                    print("Cyclic order on side 0:",
                                           tmp_cyclic_0)
                                i = len(tmp_cyclic_0)
                                break

                if not acceptable:
                    continue

                tmp_cyclic_1 = [boundary[i][2][0] for i in range(current + 1)
                                if boundary[i][2][1] == 1]
                i = 0
                if len(tmp_cyclic_1) < 2 * len(A1):
                    while i < len(tmp_cyclic_1):
                        j = i
                        done = False
                        while True:
                            aa = A1.inverse_letter(tmp_cyclic_1[j])
                            j = 0
                            while j < len(tmp_cyclic_1) and tmp_cyclic_1[
                                  j] != aa:
                                j += 1
                            if j == len(tmp_cyclic_1) or j == 0:
                                i += 1
                                break
                            j -= 1
                            if i == j:
                                acceptable = False
                                if verbose:
                                    print("There is more than one boundary "
                                           "component on side 1")
                                    print("Cyclic order on side 1:",
                                           tmp_cyclic_1)
                                i = len(tmp_cyclic_1)
                                break

                if not acceptable:
                    continue

            if current + 1 == boundary_length:
                eulerian_circuits.append(boundary[:current + 1])

            for i in range(current + 1, len(boundary)):
                e = boundary[i]
                if e[0] != boundary[current][1] or (
                        e[2][2] != 0 and -e[2][2] in oriented):
                    continue
                if e[2][1] == 0 and (cyclic_order_0 is not None) and (
                        j0 is not None):
                    jj0 = j0 + 1
                    if jj0 == len(cyclic_order_0):
                        jj0 = 0

                    if e[2][0] != cyclic_order_0[jj0]:
                        continue
                elif e[2][1] == 1 and (cyclic_order_1 is not None) and (
                        j1 is not None):
                    jj1 = j1 + 1
                    if jj1 == len(cyclic_order_1):
                        jj1 = 0
                    if e[2][0] != cyclic_order_1[jj1]:
                        continue

                next.append((e, current + 1))

        if verbose:
            print("Possible boundaries:", eulerian_circuits)

        if len(eulerian_circuits) > 1:
            print("There is an ambiguity on the choice of the "
                   "boundary of the surface.")
            print("Specify using optionnal argument cyclic_order_0 "
                   "and cyclic_order_1.")
            print("Possible choices:")
            for cyclic_order in eulerian_circuits:
                print("side 0:", [e[2][0] for e in cyclic_order if
                                  e[2][1] == 0])
                print("side 1:", [e[2][0] for e in cyclic_order if
                                  e[2][1] == 1])
            print("The first one is chosen")
        elif len(eulerian_circuits) == 0:
            print("There are no eulerian circuit in the boundary "
                   "compatible with the given cyclic orders.")
            print("Probably changing the orientation will solve this problem")
            return False

        cyclic_order = eulerian_circuits[0]

        # Now we can fix the orientation of the squares according to
        # the chosen boundary

        direct_orientation = set(e[2][2] for e in cyclic_order if e[2][2] != 0)

        for i in range(len(self.squares())):
            if orientation[i] in direct_orientation:
                orientation[i] = -1
            else:
                orientation[i] = 1

        if verbose:
            print("Orientation of the squares coherent "
                   "with the choice of the boundary")
            print(orientation)

        self._squares_orientation = orientation

        # We put the edges in the fundamental domain

        initial_vertex = dict()
        terminal_vertex = dict()

        for a in A0.positive_letters():
            aa = A0.inverse_letter(a)
            slicea = [i for i in range(len(squares)) if squares[i][4] == a]
            size = len(slicea) + 1

            if size == 1:
                continue

            # sort the edges of the slice
            i = 1
            sqi = slicea[0]
            sq = squares[sqi]
            if orientation[sqi] == 1:
                start0 = (sq[0], sq[1])
                endi = (sq[3], sq[2])
            else:
                start0 = (sq[3], sq[2])
                endi = (sq[0], sq[1])

            while i < len(slicea):
                j = i
                while j < len(slicea):
                    sqjj = slicea[j]
                    sqj = squares[sqjj]
                    if orientation[sqjj] == 1:
                        startj = (sqj[0], sqj[1])
                        endj = (sqj[3], sqj[2])
                    else:
                        startj = (sqj[3], sqj[2])
                        endj = (sqj[0], sqj[1])

                    if endi == startj:  # next(es[i-1])==es[j]:
                        slicea[j], slicea[i] = slicea[i], slicea[j]
                        i += 1
                        endi = endj
                        if i < j:
                            j = j - 1
                    elif endj == start0:  # next(es[j])==es[0]:
                        slicea = [slicea[j]] + slicea[:j] + slicea[j + 1:]
                        i += 1
                        start0 = startj
                        if i < j:
                            j = j - 1
                    j += 1

            if verbose:
                print("Slice of", a, ":", slicea)

                # put a curve for each edge of the slice
            for i, sqi in enumerate(slicea):
                sq = squares[sqi]
                if orientation[sqi] == 1:
                    initial_vertex[(sq[0], sq[3], sq[5])] = (
                        a, (i + 1.0) / size)
                    terminal_vertex[(sq[1], sq[2], sq[5])] = (
                        aa, (size - i - 1.0) / size)
                else:
                    terminal_vertex[(sq[0], sq[3], sq[5])] = (
                        a, (i + 1.0) / size)
                    initial_vertex[(sq[1], sq[2], sq[5])] = (
                        aa, (size - i - 1.0) / size)

        # We compute the regular 2N-gone that is the foundamental domain
        # of the surface on side 0

        i = 0
        while cyclic_order[i][2][1] == 1:
            i += 1

        a = A0.inverse_letter(cyclic_order[i][2][0])
        polygon_side_0 = [a]

        for j in range(2 * N - 1):
            k = 0
            while cyclic_order[k][2][1] == 1 or cyclic_order[k][2][0] != a:
                k += 1
            k -= 1
            while cyclic_order[k][2][1] == 1:
                k -= 1
                if k == 0:
                    k = boundary_length - 1
            a = A0.inverse_letter(cyclic_order[k][2][0])
            polygon_side_0.append(a)

        if verbose:
            print("Polygon bounding the fundamental domain of the surface:",
                   polygon_side_0)

        i = 0
        while polygon_side_0[i] != A0[0]:
            i += 1
        polygon_side_0 = polygon_side_0[i:] + polygon_side_0[:i]

        g = Graphics()

        boundary_initial_vertex = dict()
        boundary_terminal_vertex = dict()

        for i, a in enumerate(polygon_side_0):
            boundary_initial_vertex[a] = (
                RR(radius * cos(i * pi / N)), RR(radius * sin(i * pi / N)))
            boundary_terminal_vertex[a] = (RR(radius * cos((i + 1) * pi / N)),
                                           RR(radius * sin((i + 1) * pi / N)))

        # Regular polygon
        text_decalage = 1.05
        for a in polygon_side_0:
            x, y = boundary_initial_vertex[a]
            xx, yy = boundary_terminal_vertex[a]
            g += line([(x, y), (xx, yy)], alpha=1, thickness=2, hue=5.0 / 6)
            g += text(a, ((x + xx) / 2 * text_decalage ** 2,
                          (y + yy) / 2 * text_decalage ** 2), hue=5.0 / 6)

        for e in initial_vertex:
            a, p = initial_vertex[e]
            b = e[2]
            x = boundary_initial_vertex[a][0] + p * (
                boundary_terminal_vertex[a][0] - boundary_initial_vertex[a][0])
            y = boundary_initial_vertex[a][1] + p * (
                boundary_terminal_vertex[a][1] - boundary_initial_vertex[a][1])
            if e in terminal_vertex:
                aa, pp = terminal_vertex[e]
            else:  # the end of e is at the singularity
                i = 0
                j = 0
                while cyclic_order[i][2][1] == 0 or cyclic_order[i][2][0] != b:
                    if cyclic_order[i][2][1] == 0:
                        j = i
                    i += 1

                if j == 0 and cyclic_order[j][2][1] == 1:
                    j = len(cyclic_order) - 1
                    while cyclic_order[j][2][1] == 1:
                        j -= 1
                aa = A0.inverse_letter(cyclic_order[j][2][0])
                pp = 0

            xx = boundary_initial_vertex[aa][0] + pp * (
                boundary_terminal_vertex[aa][0] -
                boundary_initial_vertex[aa][0])
            yy = boundary_initial_vertex[aa][1] + pp * (
                boundary_terminal_vertex[aa][1] -
                boundary_initial_vertex[aa][1])

            g += line([(x, y), (xx, yy)], alpha=1, thickness=2,
                      hue=RR(A1.rank(b)) / N)

        for e in terminal_vertex:
            if e not in initial_vertex:  # the initial vertex of e is the
                # singularity
                aa, pp = terminal_vertex[e]
                xx = boundary_initial_vertex[aa][0] + pp * (
                    boundary_terminal_vertex[aa][0] -
                    boundary_initial_vertex[aa][0])
                yy = boundary_initial_vertex[aa][1] + pp * (
                    boundary_terminal_vertex[aa][1] -
                    boundary_initial_vertex[aa][1])
                b = A1.inverse_letter(e[2][0])
                i = 0
                j = 0
                while cyclic_order[i][2][1] == 0 or cyclic_order[i][2][0] != b:
                    if cyclic_order[i][2][1] == 0:
                        j = i
                    i += 1

                if j == 0 and cyclic_order[j][2][1] == 1:
                    j = len(cyclic_order) - 1
                    while cyclic_order[j][2][1] == 1:
                        j -= 1
                a = A0.inverse_letter(cyclic_order[j][2][0])
                x = boundary_initial_vertex[a][0]
                y = boundary_initial_vertex[a][1]

                g += line([(x, y), (xx, yy)], alpha=1, thickness=2,
                          hue=RR(A1.rank(b)) / N)

                g += text(e[2][0], (text_decalage * xx, text_decalage * yy),
                          hue=RR(A1.rank(b)) / N)

        for e in self.isolated_edges():
            if e[2][1] == 1:
                # The end of e is at the singularity
                b = e[2][0]
                i = 0
                j = 0
                while cyclic_order[i][2][1] == 0 or cyclic_order[i][2][0] != b:
                    if cyclic_order[i][2][1] == 0:
                        j = i
                    i += 1

                if j == 0 and cyclic_order[j][2][1] == 1:
                    j = len(cyclic_order) - 1
                    while cyclic_order[j][2][1] == 1:
                        j -= 1
                a = A0.inverse_letter(cyclic_order[j][2][0])
                x = boundary_initial_vertex[a][0]
                y = boundary_initial_vertex[a][1]

                # The start of e is also at the singularity
                bb = A1.inverse_letter(b)
                i = 0
                j = 0
                while cyclic_order[i][2][1] == 0 or cyclic_order[i][2][
                    0] != bb:
                    if cyclic_order[i][2][1] == 0:
                        j = i
                    i += 1

                if j == 0 and cyclic_order[j][2][1] == 1:
                    j = len(cyclic_order) - 1
                    while cyclic_order[j][2][1] == 1:
                        j -= 1
                aa = A0.inverse_letter(cyclic_order[j][2][0])

                xx = boundary_initial_vertex[aa][0]
                yy = boundary_initial_vertex[aa][1]

                g += line([(x, y), (xx, yy)], alpha=1, thickness=2,
                          hue=RR(A1.rank(b)) / N)

                g += text(b, (text_decalage * x, text_decalage * y),
                          hue=RR(A1.rank(b)) / N)

        for sq in self.twice_light_squares():
            b = A1.to_positive_letter(sq[5])
            # The end of b is at the singularity
            i = 0
            j = 0
            while cyclic_order[i][2][1] == 0 or cyclic_order[i][2][0] != b:
                if cyclic_order[i][2][1] == 0:
                    j = i
                i += 1

            if j == 0 and cyclic_order[j][2][1] == 1:
                j = len(cyclic_order) - 1
                while cyclic_order[j][2][1] == 1:
                    j -= 1
            a = A0.inverse_letter(cyclic_order[j][2][0])
            x = boundary_initial_vertex[a][0]
            y = boundary_initial_vertex[a][1]

            # The start of b is also at the singularity
            bb = A1.inverse_letter(b)
            i = 0
            j = 0
            while cyclic_order[i][2][1] == 0 or cyclic_order[i][2][0] != bb:
                if cyclic_order[i][2][1] == 0:
                    j = i
                i += 1

            if j == 0 and cyclic_order[j][2][1] == 1:
                j = len(cyclic_order) - 1
                while cyclic_order[j][2][1] == 1:
                    j -= 1
            aa = A0.inverse_letter(cyclic_order[j][2][0])

            xx = boundary_initial_vertex[aa][0]
            yy = boundary_initial_vertex[aa][1]

            g += line([(x, y), (xx, yy)], alpha=1, thickness=2,
                      hue=RR(A1.rank(b)) / N)

            g += text(b, (text_decalage * x, text_decalage * y),
                      hue=RR(A1.rank(b)) / N)

        g.axes(False)

        return g

    def plot_punctured_disc_ideal_curves(self, orientation=1, verbose=False):
        """
        INPUT:

        - ``orientation`` -- (default: 1): list of square  orientation
        - ``verbose`` -- (default: False) for verbose option

        .. TODO::

            not yet available

        Plot a disc with punctures and ideal curves with ``self`` as dual
        graph.

        The braid group on N starnds is the Mapping class group of the
        disc with N puntures. The fundamental group of this disc is
        the free group F_N and thus the braid group is naturally a
        subgroup of Out(F_N).

        Let p_1,...,p_N be the punctures

        Assume that ``T0`` is a tree transverse to N ideal curves a_1,
        a_2,..., a_n, where a_1 goes from a point u on the boundary to
        the first puncture p_1, a_2 goes from p_1 to p_2, a_3 from p_2
        to p_3, etc.

        Assume that ``T1`` is a tree transverse to N ideal curves
        b_1,...,b_N, where b_i goes from a common base point v on the
        boundary to p_i.

        This is the case for instance if ``T0`` and ``T1`` are marked rose
        given by ``MarkedGraph.rose_marked_graph(alphabet)``, and ``T1``
        has been precomposed by an automorphism ``phi`` given by as a product
        of ``F.braid_automorphism(i)``.

        Note that in this context there are no twice light squares.

        EXAMPLES::

            sage: from train_track import *
            sage: from train_track.convex_core import ConvexCore
            sage: F=FreeGroup('a,b,c,d')
            sage: phi=mul([FreeGroupAutomorphism.surface_dehn_twist(F,i) for i in [2,1,1,4]])
            sage: C=ConvexCore(phi)
            sage: C.plot_punctured_disc_ideal_curves()  # todo: not implemented


        """
        from sage.plot.graphics import Graphics
        from sage.plot.line import Line
        from sage.plot.arrow import Arrow

        T0 = self.tree(0)
        T1 = self.tree(1)
        A0 = T0.alphabet()
        N = len(A0)

        # Coherent orientation of the squares

        orientation = self.squares_orientation(
            orientation=orientation,
            verbose=verbose and verbose > 1 and verbose - 1)

        if verbose:
            print("Orientation of the squares:")
            if verbose > 1:
                for i, sq in enumerate(squares):
                    print(i, ":", sq, ":", orientation[i])

                    # Edges of the boundary

        boundary = self.surface_boundary(
            orientation=orientation,
            verbose=verbose and verbose > 1 and verbose - 1)

        if verbose:
            print("Edges of the boundary:")
            print(boundary)

        # TODO


