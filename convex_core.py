#*****************************************************************************
#       Copyright (C) 2013 Matt Clay and Thierry Coulbois
#       <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.combinat.words.word import Word
from sage.graphs.graph import DiGraph
from inverse_graph import GraphWithInverses
from inverse_graph import MetricGraph


class ConvexCore():
    """Guirardel's convex core of two simplicial trees with an action of
    a free group.

    Let T1 and T2 be trees with actions of the free group FN. G1=T1/FN
    and G2=T2/FN are MarkedGraph. 

    A ConvexCore is a CW-complex of dimension 2. 2-cells are
    squares. 1 cells are edges labeled by edges of G1 or G2. A square
    is of the form

          e
        ----->
       |      |
     f |      | f
       |      |
       v      v
        ----->
          e

    where e is an edge of G1 and f an edge of G2.

    MetricGraph with edges of length 0 can be used for trees with a
    non-free action of FN. 

    ``ConvexCore(phi)``: where ``phi`` is an automorphism of the free
    group F. The convex core of the Cayley tree TA of the free group F
    with respect to its alphabet A, and of the tree TA.Phi, where Phi
    is the outer class of ``phi``.

    ``ConvexCore(G1,G2)``: where ``G1`` and ``G2`` are two marked
    graphs (or two marked metric graphs): The convex core of the
    universal covers T1 and T2 of ``G1`` and ``G2``
    respectively. Edges of length 0 are quotient out.

    ``ConvexCore(f)``: where ``f`` is a homotopy equivalence between
    graphs G1 and G2: The convex core of the universal covers T1 and
    T2 of G1 and G2, with the fundamental group F of G1 acting on G2
    through ``f``. Edges of length 0 are quotient out.

    TODO:

    Does not detect edges which do not bound a square.

    WARNING:

    It is assumed that boths graphs G1 and G2 does not have vertices
    of valence 1 or 2.

    The one squeleton may fail to be connected due to absence of some
    isolated edges.

    There might be a problem if the labels of the edges are not
    coherently positive. Indeed there is a choice of a fundamental
    domain around the base point in the tree.

    AUTHORS:

    - Matt Clay
    
    Modified by Thierry Coulbois

    """

    def __init__(self,*args):
        if len(args)==2: #ConvexCore(G,H)
            G0=args[0]
            G1=args[1]
            f=G0.difference_of_marking(G1).tighten()
            g=f.inverse()
        elif len(args)==1:
            if isinstance(args[0],GraphMap): #ConvexCore(f)
                G0=f.domain()
                G1=f.codomain()
                f=args[0]
                g=f.inverse()
            elif isinstance(args[0],FreeGroupAutomorphism): # ConvexCore(phi)
                f=args[0]
                A=f.domain().alphabet()
                G0=GraphWithInverses.rose_graph(A)
                G1=GraphWithInverses.rose_graph(A)
                g=f.inverse()
        elif len(args)==4: #ConvexCore(G,H,f,g)
            (G0,G1,f,g)=args


        self._G0=G0
        self._G1=G1

        self._f01=f  #WARNING: it is necessary that f maps the base
                     #point of G0 to the base point of G1 and
                     #conversely
        self._f10=g

        A0=G0.alphabet()
        A1=G1.alphabet()

        self._build_signed_ends()

        signed_ends=self._signed_ends

        two_cells=set([]) # A 2-cell is a triple (path,a,b) with a,b
                          # positive letters of A0 and A1 and path a
                          # reduced path in G0 from V0 to the initial
                          # vertex of a

        isolated_one_cells=set()  # Edges that are not boundaries of two-cells
        existing_edges=dict(((a,0),False) for a in A.positive_letters())+dict(((b,1),False) for b in B.positive_letters)

        twice_light_squares=[] # a twice light quadrant stored as
                               # (w,a,b) where w is a path in G0
                               # starting at v0 and ending at
                               # G0.initial_vertex(a). b is a positive
                               # letter in A1. The vertex at the end
                               # of w is in the convex core.
                

        # close the slices by convexity
        for b in A1.positive_letters():
            empty_slice=True
            if len(signed_ends[b])>0:
                common=signed_ends[b][0][0]
            for (w,sign) in signed_ends[b]:
                common_len=G0.common_prefix_length(common,w)
                if common_len<len(common):
                    common=common[:common_len]
            for (w,sign) in signed_ends[b]:
                for i in xrange(common_len,len(w)-1):
                    a=w[i]
                    empty_slice=False
                    if A0.is_positive_letter(a):
                        existing_edges[(a,0)]=True
                        two_cells.add((w[:i],a,b))
                    else:
                        aa=A0.inverse_letter(a)
                        existing_edges[(aa,0)]=True
                        two_cells.add((w[:i+1],aa,b))
            if empty_slice: # we need to check wether we add an isolated edge
                if len(signed_ends[b])>1:
                    isolated_b=len(common)>0
                    if not isolated_b: # we need at least two edges out of v0 without +
                        v0=G0.intial_vertex[A0[0]]
                        outgoing_from_origin=[a for a in A0 if G0.initial_vertex(a)==v0]
                    isolated_b=isolated_b or len(signed_ends[b])+1>len(outgoing_from_origin)
                    if isolated_b:
                        existing_edges[(b,1)]=True
                        isolated_one_cells.add((common,b,1))  # common stands for its terminal vertex
                    else: #len(signed_ends[b])+1=len(outgoing_from_origin) and len(common)==0
                        positive_outgoing_edges=[e[0][0] for e in signed_ends[b]]  
                        for a in outgoing_from_origin: # we look for the only edge outgoing from the origin without a +
                            if a not in positive_outgoing_edges:
                                break

                        existing_edges[(b,1)]=True
                        twice_light_squares.append((common,a,b)) # note that common=Word([])
                        if A0.is_positive_letter(a):
                            existing_edges[(a,0)]=True
                        else:
                            aa=A0.inverse_letter(a)
                            existing_edges[(aa,0)]=True
                else: #len(signed_ends[b]==1)
                    a=common[-1]
                    existing_edges[(b,1)]=True
                    twice_light_squares.append((common[:-1],a,b))
                    if A0.is_positive_letter(a):
                        existing_edges[(a,0)]=True
                    else:
                        aa=A0.inverse_letter(a)
                        existing_edges[(aa,0)]=True
            else: 
                existing_edges[(b,1)]=True

        # we check for isolated vertices they are the corners of twice rectangles.
        isolated_vertices=[]
        missing_edges=dict([])
        for (w,a,b) in twice_light_rectangles:
            missing_edges[G1.initial_vertex(b)].append(b)
        for v in missing_edges.keys():
            if len(missing_edges[v])==len(G1.outgoing_edges(v)):
                isolated_vertex.append(w,v)


        # we check for isolated edges of the form (a,0)
        for a in A0.positive_letters():
            if not existing_edges[(a,0)]:
                for b in B.positive_letters():
                    pass #TODO


        # create the convex core as a square complex
        
        one_cells_G=set()  # there are two kinds of edges: those from G and those from H
        one_cells_H=set()
        two_cell_boundary=dict() # The boundary operator that map a 2-cell to the 4 edges of its boundary
        zero_cells=set() # vertices
        one_cell_G_boundary=dict()
        one_cell_H_boundary=dict()


        # TODO: il faut echanger a et b, maintenant dans (w,a,b) w est un chemin dans G.

        for (v,a,b) in two_cells:
            vb=H.reduce_path(v*Word([b]))
            Av=H.reduce_path(f.image(A.inverse_letter(a))*v)
            one_cells_H.add((v,b))
            one_cells_H.add((Av,b))
            one_cells_G.add((v,a))
            one_cells_G.add((vb,a))
            two_cell_boundary[(v,a,b)]=(((v,a),(vb,a),(v,b),(Av,b)))
            zero_cells.add(v)
            zero_cells.add(vb)
            zero_cells.add(Av)
            Avb=H.reduce_path(Av*Word([b]))
            zero_cells.add(Avb)
            one_cell_H_boundary[(v,b)]=(v,vb)
            one_cell_H_boundary[(Av,b)]=(Av,Avb)
            one_cell_G_boundary[(v,a)]=(v,Av)
            one_cell_G_boundary[(vb,a)]=(vb,Avb)

        one_cell_G_class=dict((e,i) for i,e in enumerate(one_cells_G))
        one_cell_H_class=dict((e,i) for i,e in enumerate(one_cells_H))

        for c in two_cells:
            if isinstance(G,MetricGraph) and G.length(c[1])==0:
                j=one_cell_H_class[two_cell_boundary[c][2]]
                k=one_cell_H_class[two_cell_boundary[c][3]]
                if j!=k:
                    for e in one_cell_H_class:
                        if one_cell_H_class[e]==k:
                            one_cell_H_class[e]=j
            if isinstance(H,MetricGraph) and H.length(c[2])==0:
                j=one_cell_G_class[two_cell_boundary[c][0]]
                k=one_cell_G_class[two_cell_boundary[c][1]]
                if j!=k:
                    for e in one_cell_G_class:
                        if one_cell_G_class[e]==k:
                            one_cell_G_class[e]=j

        zero_cell_class=dict((v,i) for i,v in enumerate(zero_cells))
        if isinstance(G,MetricGraph):
            for e in one_cells_G:
                if G.length(e[1])==0:
                    j=zero_cell_class[one_cell_G_boundary[e][0]]
                    k=zero_cell_class[one_cell_G_boundary[e][1]]
                    if j!=k:
                        for v in zero_cells:
                            if zero_cell_class[v]==k:
                                zero_cell_class[v]=j

        if isinstance(H,MetricGraph):
            for e in one_cells_H:
                if H.length(e[1])==0:
                    j=zero_cell_class[one_cell_H_boundary[e][0]]
                    k=zero_cell_class[one_cell_H_boundary[e][1]]
                    if j!=k:
                        for v in zero_cells:
                            if zero_cell_class[v]==k:
                                zero_cell_class[v]=j
        i=0
        map_G=dict()
        for e in one_cells_G:
            j=one_cell_G_class[e]
            if j not in map_G:
                map_G[j]=i
                i+=1
        map_H=dict()
        for e in one_cells_H:
            j=one_cell_H_class[e]
            if j not in map_H:
                map_H[j]=i
                i+=1


        i=0
        boundary_2=dict()
        label_2=dict()
        for c in two_cells:
            if ((not isinstance(G,MetricGraph)) or G.length(c[1])>0) \
                    and ((not isinstance(H,MetricGraph)) or H.length(c[2])>0):
                (a,b,bb,d)=two_cell_boundary[c]
                boundary_2[i]=(map_G[one_cell_G_class[a]],map_G[one_cell_G_class[b]],map_H[one_cell_H_class[bb]],map_H[one_cell_H_class[d]])
                label_2[i]=(c[1],c[2])
                i+=1

        boundary_1=dict()
        label_1=dict()
        for e in one_cells_G:
             if (not isinstance(G,MetricGraph)) or G.length(e[1])>0:
                 i=map_G[one_cell_G_class[e]]
                 (v,vv)=one_cell_G_boundary[e]
                 boundary_1[i]=(zero_cell_class[v],zero_cell_class[vv])
                 label_1[i]=(e[1],0)
        for e in one_cells_H:
             if (not isinstance(H,MetricGraph)) or H.length(e[1])>0:
                 i=map_H[one_cell_H_class[e]]
                 (v,vv)=one_cell_H_boundary[e]
                 boundary_1[i]=(zero_cell_class[v],zero_cell_class[vv])
                 label_1[i]=(e[1],1)

        zero_cells=set(zero_cell_class[v] for v in zero_cells)

        self._zero_cells=zero_cells
        self._boundary_2=boundary_2
        self._boundary_1=boundary_1
        self._label_1=label_1
        self._label_2=label_2

    def _build_signed_ends(self):
        """For each edge of G1 computes a list of edges in T0 assigned with a + or a - sign.

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
        G0 and G1 based at v0 and v1. We choose the lifts of f and g
        that maps v0 to v1 and conversely.

        Fix an edge e1 in T1. An edge e0 in T0 is assigned a + if its
        image f(e0) crosses e1 positively.


        """
        G0=self._G0
        G1=self._G1

        f=self._f01
        g=self._f10

        A0=G0.alphabet()
        A1=G1.alphabet()


        t0=G0.spanning_tree()
        t1=G1.spanning_tree()

        # the positive letter b in A1 stands for the edge (t1(b),b) of
        # the universal cover of G1 (where t1(b) is the path in t1
        # from the root to the initial vertex of b). WARNING: with
        # this definition the edge b may not be oriented away from the
        # base point v1.
         
        signed_ends=dict((b,[]) for b in A1.positive_letters())

        for a in A0.positive_letters():
            aa=A0.inverse_letter(a)
            image_a=f.image(a)
            w=t0[G0.initial_vertex(a)]
            w=G0.reduced_path(g(f(G0.reverse_path(w)))*w)
            for b in image_a: # the image f(a) crosses the edge prefix.b
                pb=A1.to_positive_letter(b)
                u0=g(t1[G1.initial_vertex(pb)])
                if b==pb:
                    w0=G0.reduced_path(u0*w)
                    if len(w0)==0 or w0[-1]!=A0.inverse_letter(a):
                        signed_ends[pb].append((w0*Word([a],'+')))
                    else:
                        signed_ends[pb].append((w0,'-'))
                w=G0.reduced_path(g.image(A1.inverse_letter(b))*w))
                if b!=pb:
                    w0=G0.reduced_path(u0*w)
                    if len(w0)==0 or w0[-1]!=A0.inverse_letter(a):
                        signed_ends[pb].append((w0*Word([a]),'-'))
                    else:
                        signed_ends[pb].append((w0,'+'))


        self._signed_ends=signed_ends
        
    def tree(self,side):
        """
        ``T0`` or ``T1`` (according to ``side``) where ``self`` is the
        convex core of the trees ``T0`` and ``T1``.

        """
        if side==0:
            return self._T0
        else:
            return self._T1

    def two_cells(self):
        """
        List of two cells (ie squares) of ``self``.
        """
        return self._boundary_2.keys()

    def one_cells(self):
        """
        List of one cells (ie edges) of ``self``.
        """
        return self._boundary_1.keys()


    def zero_cells(self):
        """
        Set of zero cells (vertices) of ``self``.
        """
        return self._zero_cells


    def boundary_2(self,c):
        """
        Boundary of the two-cell ``c``.

        OUTPUT:

        A tuple ``(e,f,g,h)`` of four one-cells. ``e`` and ``f`` are
        labeled by ``(a,0)`` for some edge ``a`` of the tree ``T0``,
        while ``g`` an ``h`` are labeled by ``(b,1)`` for some edge
        ``b`` of ``T1``.
        """

        return self._boundary_2[c]


    def boundary_1(self,e):
        """
        Boundary of the one_cell ``e``.

        OUTPUT:

        ``(u,v)``: the initial vertex ``u`` and the terminal
        vertex ``v`` of ``e``.
        """

        return self._boundary_1[e]

    def label_2(self,c):
        """
        Label of the two-cell ``c``.

        OUTPUT:

        ``(a,b)`` where ``a`` is an edge of ``T0`` and ``b`` is an
        edge of ``T1``.
        """

        return self._label_2[c]

    def label_1(self,e):
        """
        Label of the one-cell ``e``.

        OUTPUT:

        ``(a,side)`` where ``side`` is 0 or 1 and ``a`` is an edge of
        ``Tside``.

        """

        return self._label_1[e]



    def slice(self,a,side):
        """
        Slice of ``self`` for the edge ``a`` of the given ``side``.

        The slice is the tree whose vertices are edges labeled by
        ``(a,side)`` and with edges the two cells with one side
        corresponding to ``(a,side)``.

        OUTPUT:

        A ``DiGraph``, edges are labeled by the corresponding
        two-cells of ``self``.

        INPUT:

        If ``self`` is the core of the trees ``T0`` and ``T1`` and
        ``side==0`` then ``a`` is an edge of ``T0``. Conversely if
        ``side==1`` then ``a`` is an edge of ``T1``.
        """

        G=DiGraph(loops=True,multiedges=True)
        for (i,b) in self._boundary_2.iteritems():
            if self.label_1(b[2*side])[0]==a:
                G.add_edge(b[2*side],b[2*side+1],i)

        return G


    def one_squeleton(self,side):
        """
        One squeleton of ``self`` on the ``side``

        INPUT:

        ``side`` is 0 or 1, standing for ``T0`` or ``T1``


        OUTPUT:

        A ``GraphWithInverses`` with the same alphabet than ``Tside``
        """

        G=self.tree(side)
        A=G.alphabet()
        result=GraphWithInverses(alphabet=A)

        for (i,b) in self._boundary_1.iteritems():
            if self.label_1(i)[1]==side:
                result.add_edge(b[0],b[1],self.label_1(i)[0])

        return result

    def volume(self):
        """
        Volume of ``self``.

        If the trees are not metric trees then this is the simplicial
        volume: the number of squares in the 2-squeleton. 
        
        If the trees are metric trees, then this is the volume.
        """

        if isinstance(self.tree(0),MetricGraph) and isinstance(self.tree(1),MetricGraph): 
            result=0
            for  (a,b) in self._label_2.itervalues():
                result+=self.tree(0).length(a)*self.tree(1).length(b)
            return result
        elif isinstance(self.tree(0),MetricGraph):
            result=0
            for (a,b) in self._label_2.itervalues():
                result+=self.tree(0).length(a)
            return result
        elif isinstance(self.tree(1),MetricGraph):
            result=0
            for (a,b) in self._label_2.itervalues():
                result+=self.tree(1).length(b)
            return result
        else:
            return len(self._boundary_2)

    def ideal_curve_diagram(self,radius=1,orientation=1,boundary_word=None):
        """
        
        An ideal curve diagram on the once punctured surface S of
        genus g which is transverse to the core.

        Only works if T0 was the tree transverse to the original set
        of ideal curves and T1 is the image of T0 by a maaping class
        of S (not a general outer automorphism).

        INPUT:

        - ``orientation``: ``1`` or ``-1`` (default 1) whether the first 2-cell of
          ``self`` is positively oriented or not.
        

        - ``radius``: (default 1) the radius of the regular n-gone
          which is the fondamental domain of the surface.
        """

        from sage.plot.line import Line
        from sage.plot.arrow import Arrow
        
        #        boundary_word=Word("AbaBDCdc")
        #        boundary_word=Word("bABaCDcd")
        #        boundary_word=Word("baBDCdcA")
        #    boundary_word=Word("ABabDcdC")
        #    boundary_word=Word("abABdCDc")
        #    boundary_word=Word("BAbacDCd")
        
        A=self.tree(0).alphabet()
        N=len(A)
        

        # orientation of 2-cells
            
        orient=orientation
        orientation=dict()

        orientation[self.two_cells()[0]]=orient
        queue=[self.two_cells()[0]]
        while len(queue)>0:
            c0=queue.pop()
            e10,e20,f10,f20=self.boundary_2(c0)
            for c in self.two_cells():
                if c not in orientation:
                    e1,e2,f1,f2=self.boundary_2(c)
                    if e1==e10 or e2==e20 or f1==f10 or f2==f20:
                        orientation[c]=-orientation[c0]
                        queue.append(c)
                    elif e1==e20 or e2==e10 or f1==f20 or f2==f10:
                        orientation[c]=orientation[c0]
                        queue.append(c)


        initial_vertex=dict()
        terminal_vertex=dict()

        boundary_edges_orientation=dict()

        for a in A.positive_letters():
            aa=A.inverse_letter(a)
            s=self.slice(a,0)
            es=s.edges()
            size=len(es)+1

            if size==1:
                continue

            # sort the edges of the slice
            i=1
            start0=es[0][(1-orientation[es[0][2]])/2]
            endi=es[i-1][(1+orientation[es[i-1][2]])/2]    

            while i<len(es):
                j=i
                while j<len(es):
                    startj=es[j][(1-orientation[es[j][2]])/2]
                    endj=es[j][(1+orientation[es[j][2]])/2]    
                    
                    if endi==startj: # next(es[i-1])==es[j]:
                        es[j],es[i]=es[i],es[j]
                        i+=1
                        endi=endj
                        if i<j:
                            j=j-1
                    elif endj==start0: #next(es[j])==es[0]:
                        es=[es[j]]+es
                        es[j+1:j+2]=[]
                        i+=1
                        start0=startj
                        if i<j:
                            j=j-1
                    j+=1


            # put a curve for each edge of the slice
            for i,e in enumerate(es):
                if orientation[e[2]]==1:
                    initial_vertex[self.boundary_2(e[2])[2]]=(a,(i+1.0)/size)
                    terminal_vertex[self.boundary_2(e[2])[3]]=(aa,(size-i-1.0)/size)
                else:
                    terminal_vertex[self.boundary_2(e[2])[2]]=(a,(i+1.0)/size)
                    initial_vertex[self.boundary_2(e[2])[3]]=(aa,(size-i-1.0)/size)

            e=es[0]
            boundary_edges_orientation[e[(1-orientation[e[2]])/2]]=-1
            e=es[-1]
            boundary_edges_orientation[e[(1+orientation[e[2]])/2]]=1
            
        for e in initial_vertex:
            if e not in terminal_vertex:
                boundary_edges_orientation[e]=1
        for e in terminal_vertex:
            if e not in initial_vertex:
                boundary_edges_orientation[e]=-1
                

        # order the boundary

        incomplete_boundary=False

        boundary=boundary_edges_orientation.keys()
        i=1
        e0=boundary[0]
        if boundary_edges_orientation[e0]==1:
            start0,endi=self.boundary_1(e0)
        else:
            endi,start0=self.boundary_1(e0)
        while i<len(boundary):
            j=i
            skip=True
            while j<len(boundary):
                e=boundary[j]
                if boundary_edges_orientation[e]==1:
                    startj,endj=self.boundary_1(e)
                else:
                    endj,startj=self.boundary_1(e)
                if endi==startj:
                    boundary[i],boundary[j]=boundary[j],boundary[i]
                    endi=endj
                    i=i+1
                    if i<j:
                        j=j-1
                    skip=False
                elif start0==endj:
                    boundary=[boundary[j]]+boundary
                    boundary[j+1:j+2]=[]
                    start0=startj
                    i+=1
                    if i<j:
                        j=j-1
                    skip=False
                j+=1
            if skip:
                i+=1
                
                incomplete_boundary=True

        # disc bounded by ideal curves
        disc_0=[A[0]]


        while len(disc_0)<2*N:
            a=disc_0[-1]
            done=False
            j=len(boundary)-1
            while j>=0 and not done:
                if self.label_1(boundary[j])[1]==0:
                    e=boundary[j]
                    b=self.label_1(e)[0]
                    if boundary_edges_orientation[e]==-1:
                        b=A.inverse_letter(b)
                    if a==b:
                        done=True
                j-=1

            if j<0: j=len(boundary)-1
            while self.label_1(boundary[j])[1]==1:
                j-=1
                if j<0: j=len(boundary)-1
            e=boundary[j]
            b=self.label_1(e)[0]
            if boundary_edges_orientation[e]==1:
                b=A.inverse_letter(b)
            disc_0.append(b)

        print "disc",
        for a in disc_0:
            print a,
        print
        print "boundary",
        for e in boundary:
            a,i=self.label_1(e)
            if boundary_edges_orientation[e]==-1:
                a=A.inverse_letter(a)
            print "{0}_{1}".format(a,i),

        # we now fix the ideal curves starting from corners
            
        i=0
        while self.label_1(boundary[i])[1]==1:
            i+=1

        previous_letter=self.label_1(boundary[i])[0]
        if boundary_edges_orientation[boundary[i]]==-1:
            previous_letter=A.inverse_letter(previous_letter)
        
        j=i-1
        if j<0: j=len(boundary)-1
        while j!=i:
            e=boundary[j]
            if self.label_1(e)[1]==0:
                previous_letter=self.label_1(e)[0]
                if boundary_edges_orientation[e]==-1:
                    previous_letter=A.inverse_letter(previous_letter)
            else:
                if boundary_edges_orientation[e]==1:
                    terminal_vertex[e]=(previous_letter,1)
                else:
                    initial_vertex[e]=(previous_letter,1)
            j-=1
            if j<0:
                j=len(boundary)-1

        g=Graphics()

        boundary_initial_vertex=dict()
        boundary_terminal_vertex=dict()

        for i,a in enumerate(disc_0):
            boundary_initial_vertex[a]=(RR(radius*cos(i*pi/N)),RR(radius*sin(i*pi/N)))
            boundary_terminal_vertex[a]=(RR(radius*cos((i+1)*pi/N)),RR(radius*sin((i+1)*pi/N)))


        # Regular polygon
        text_decalage=1.05
        for a in disc_0:
            x,y=boundary_initial_vertex[a]
            xx,yy=boundary_terminal_vertex[a]
            g+=line([(x,y),(xx,yy)],alpha=1,thickness=2,hue=5.0/6)
            g+=text(a,((x+xx)/2*text_decalage**2,(y+yy)/2*text_decalage**2),hue=5.0/6)

            #Line([boundary_initial_vertex[a][0],boundary_terminal_vertex[a][0]],\
            #   [boundary_initial_vertex[a][1],boundary_terminal_vertex[a][1]],\
            #  {'alpha':1,'thickness':2,'rgbcolor':(0,1,1),'legend_label':''})
 

        for e in initial_vertex:
            if e in terminal_vertex:
                a,p=initial_vertex[e]
                aa,pp=terminal_vertex[e]
                b=self.label_1(e)[0]
                x=boundary_initial_vertex[a][0]+p*(boundary_terminal_vertex[a][0]-boundary_initial_vertex[a][0])
                y=boundary_initial_vertex[a][1]+p*(boundary_terminal_vertex[a][1]-boundary_initial_vertex[a][1])
                xx=boundary_initial_vertex[aa][0]+pp*(boundary_terminal_vertex[aa][0]-boundary_initial_vertex[aa][0])
                yy=boundary_initial_vertex[aa][1]+pp*(boundary_terminal_vertex[aa][1]-boundary_initial_vertex[aa][1])
                if p==1:
                    g+=text(b,(text_decalage*xx,text_decalage*yy),hue=RR(A.rank(b))/N)
                
                g+=line([(x,y),(xx,yy)],alpha=1,thickness=2,hue=RR(A.rank(b))/N)
                

#ar=Line([x,xx],[y,yy],{'alpha':1,'thickness':2,'rgbcolor':color[b],'legend_label':''}) #{'width':3,'head':1,'rgbcolor':(1,0,0),'linestyle':'dashed','zorder':8,'legend_label':''})
#                g.add_primitive(ar)
        
        g.axes(False)

        return g

        


        

        
        
