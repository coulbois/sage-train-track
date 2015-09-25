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
from graph_map import GraphMap
from free_group_automorphism import FreeGroupAutomorphism
import bisect

class ConvexCore():
    """Guirardel's convex core of two simplicial trees with an action of
    a free group.

    Let T1 and T2 be trees with actions of the free group FN. G1=T1/FN
    and G2=T2/FN are MarkedGraph. 

    A ConvexCore is a CW-complex of dimension 2. 2-cells are
    squares. 1-cells are edges labeled by edges of G1 or G2. A square
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

    WARNING:

    It is assumed that boths graphs G1 and G2 do not have vertices
    of valence 1 or 2.

    EXAMPLES::

    sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")
    sage: phi=phi*phi
    sage: C=ConvexCore(phi)
    sage: print C.slice('c',0)
    Looped multi-digraph on 2 vertices

    sage: C.vertices()
    [0, 1, 2, 3]

    sage: C.squares()
    [[3, 0, 2, 1, 'c', 'a']]
    
    sage: twice_light_squares()
    [[1, 4, 0, 5, 'a', 'c']]

    AUTHORS:

    - Matt Clay
    
    Modified by Thierry Coulbois

    """

    def __init__(self,*args,**keywords):
        if 'verbose' in keywords:
            verbose=keywords['verbose']
        else:
            verbose=False
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
                f=args[0].simple_outer_representative()
                A=f.domain().alphabet()
                G0=GraphWithInverses.rose_graph(A)
                G1=GraphWithInverses.rose_graph(A)
                g=f.inverse()
        elif len(args)==4: #ConvexCore(G,H,f,g)
            (G0,G1,f,g)=args


        self._G0=G0
        self._G1=G1
        
        t1=G1.spanning_tree(verbose=(verbose and verbose>1 and verbose-1))
        t0=G0.spanning_tree(verbose=(verbose and verbose>1 and verbose-1))
        self._t0=t0
        self._t1=t1
        
        self._f01=f  #WARNING: it is necessary that f maps the base
                     #point of G0 to the base point of G1 and
                     #conversely
        self._f10=g
        
        # In the sequel t1 is G1.spanning_tree() with v1 as root
        # (similarly v0 is the root of G0.spanning_tree()). A vertex in
        # T0 is designated by a path w from v0. An edge in T0 is
        # designated by (w,a) where w is path from v0 to the initial
        # vertex of a. Note that wa need not be reduced.  A vertex v
        # in G1 designates the vertex at the end of the path t1(v)
        # from v0. A positive letter b in A1 with initial vertex v
        # designates the edge (t1(v),b) in T1 (again t1(v)b need not
        # be reduced).

        A0=G0.alphabet()
        A1=G1.alphabet()

        if verbose: print "Building signed ends"
        self._build_signed_ends(verbose=(verbose and verbose>1 and (verbose-1)))

        signed_ends=self._signed_ends
        
        heavy_squares=[] # A 2-cell is a triple (w,v,a,b) with a,b
                          # positive letters of A0 and A1 and w a
                          # reduced path in G0 from v0 to the initial
                          # vertex of a. v is the initial vertex of b
                          # in G1. The edge b stands for the edge
                          # t1(b)b.

        isolated_edges=[]  # Edges that are not boundaries of
                               # two-cells stored as (w,v,(b,1)) with
                               # w a path in G0 starting at v0 and b a
                               # positive letter in A1 standing for an
                               # edge in T1 as above. Again v is the
                               # initial vertex of b in G1.

        existing_edges=dict(((a,0),False) for a in A0.positive_letters())
        for b in A1.positive_letters():
            existing_edges[(b,1)]=False
                    
        twice_light_squares=[] # a twice light square stored as
                               # (w,v,a,b) where w is a path in G0
                               # starting at v0 and ending at
                               # u=G0.initial_vertex(a). a is a letter
                               # in A0 (not necessarily positive). b
                               # is a positive letter in A1 standing
                               # for an edge between the vertices
                               # v=G1.initial_vertex(b) and v.b in
                               # T1 as above. The corners (w,v) and
                               # (w.a,v.b) are in the convex core.
        
        isolated_vertices=[] #An isolated vertex stored as (w,v) where
                             #w is a path in G0 starting at v0 and v
                             #is a vertex in G1 lifted in T1 as above
        
        # close the slices by convexity
        for b in A1.positive_letters():
            if verbose: print "Building the slice of",b
            empty_slice=True
            if len(signed_ends[b])>0:
                signed_ends[b].sort()
                if verbose>1: print "Signed ends of ",b,":",signed_ends[b]
                common=signed_ends[b][0][0]
            for (w,sign) in signed_ends[b]:
                common_len=G0.common_prefix_length(common,w)
                if common_len<len(common):
                    common=common[:common_len]
                    if common_len==0: break
            wp=common
            for (w,sign) in signed_ends[b]:
                start=G0.common_prefix_length(wp,w)
                if start==len(wp) and start>common_len:
                    start-=1
                wp=w
                for i in xrange(start,len(w)-1):
                    a=w[i]
                    empty_slice=False
                    if A0.is_positive_letter(a):
                        existing_edges[(a,0)]=True
                        heavy_squares.append((w[:i],G1.initial_vertex(b),a,b))
                        if verbose: print "Heavy square", heavy_squares[-1]
                    else:
                        aa=A0.inverse_letter(a)
                        existing_edges[(aa,0)]=True
                        heavy_squares.append((w[:i+1],G1.initial_vertex(b),aa,b))
                        if verbose: print "Heavy square", heavy_squares[-1]
            if empty_slice: # we need to check wether we add an isolated edge
                if verbose: print "The slice of",b,"is empty, looking for an isolated edge"
                if len(signed_ends[b])>1:
                    isolated_b=len(common)>0
                    if not isolated_b: # we need at least two edges out of v0 without +
                        v0=G0.initial_vertex(A0[0])
                        outgoing_from_origin=[a for a in A0 if G0.initial_vertex(a)==v0]
                        isolated_b=isolated_b or len(signed_ends[b])+1<len(outgoing_from_origin)
                    if isolated_b:
                        existing_edges[(b,1)]=True
                        isolated_edges.append((common,G1.initial_vertex(b),(b,1)))  # common stands for its terminal vertex
                        if verbose: print "Isolated edge",(common,b,1)
                    else: #len(signed_ends[b])+1==len(outgoing_from_origin) and len(common)==0
                        positive_outgoing_edges=[e[0][0] for e in signed_ends[b]]  
                        for a in outgoing_from_origin: # we look for the only edge outgoing from the origin without a +
                            if a not in positive_outgoing_edges:
                                break

                        existing_edges[(b,1)]=True
                        if signed_ends[b][0][1]=='+':
                            twice_light_squares.append((Word([a]),G1.initial_vertex(b),A0.inverse_letter(a),b)) # note that common=Word([])
                            if verbose: print "Twice-light square (type 1)",twice_light_squares[-1]
                        else:
                            twice_light_squares.append((common,G1.initial_vertex(b),a,b))
                            if verbose: print "Twice-light square (type 2)",twice_light_squares[-1]
                        if A0.is_positive_letter(a):
                            existing_edges[(a,0)]=True
                        else:
                            aa=A0.inverse_letter(a)
                            existing_edges[(aa,0)]=True
                else: #len(signed_ends[b]==1)
                    a=common[-1]
                    existing_edges[(b,1)]=True
                    if signed_ends[b][0][1]=='-':
                        twice_light_squares.append((common,G1.initial_vertex(b),A0.inverse_letter(a),b))
                        if verbose: print "Twice-light square (type 3)",twice_light_squares[-1]
                    else:
                        twice_light_squares.append((common[:-1],G1.initial_vertex(b),a,b))
                        if verbose: print "Twice-light square (type 4)",twice_light_squares[-1]   
                    if A0.is_positive_letter(a):
                        existing_edges[(a,0)]=True
                    else:
                        aa=A0.inverse_letter(a)
                        existing_edges[(aa,0)]=True
            else: 
                existing_edges[(b,1)]=True

        # we check for isolated and semi-isolated vertices (vertices
        # without an adjacent edge of the form (b,1)): they are
        # surrounded by twice light squares.
        semi_isolated_vertices=[]
        adjacent_twice_light_squares=dict([])
        if verbose: print "Looking for isolated vertices"
        for (w,v,a,b) in twice_light_squares:
            if (v,1) in adjacent_twice_light_squares:
                adjacent_twice_light_squares[(v,1)].append(w)
            else:
                adjacent_twice_light_squares[(v,1)]=[w]

            w=w*Word([a]) 
            vv=G1.terminal_vertex(b)
            u=G1.reduce_path(t1[vv]*G1.reverse_path(t1[v]*Word([b])))
            if len(u)>0:  #if vv does not stand for v.b
                w=G0.reduce_path(g(u)*w)
            if (vv,1) in adjacent_twice_light_squares:
                adjacent_twice_light_squares[(vv,1)].append(w)
            else:
                adjacent_twice_light_squares[(vv,1)]=[w]
                

            # b=self.boundary((w,v,a,b))
            # ww,vv=b[1][1]
            # if (vv,1) in adjacent_twice_light_squares:
            #     adjacent_twice_light_squares[(vv,1)].append(ww)
            # else:
            #     adjacent_twice_light_squares[(vv,1)]=[ww]
                
            u0=G0.initial_vertex(a)
            if (u0,0) in adjacent_twice_light_squares:
                adjacent_twice_light_squares[(u0,0)]+=1
            else:
                adjacent_twice_light_squares[(u0,0)]=1
                
            uu0=G0.terminal_vertex(a)
            if (uu0,0) in adjacent_twice_light_squares:
                adjacent_twice_light_squares[(uu0,0)]+=1
            else:
                adjacent_twice_light_squares[(uu0,0)]=1

        for (v,i) in adjacent_twice_light_squares.keys():
            if i==1 and len(adjacent_twice_light_squares[(v,1)])==G1.degree(v): # v is a semi-isolated vertex
                w=adjacent_twice_light_squares[(v,1)][0]
                if len(w)>0:
                    u0=G0.terminal_vertex(w)
                else:
                    u0=G0.initial_vertex(A0[0])
                if adjacent_twice_light_squares[(u0,0)]==G0.degree(u0):
                    isolated_vertices.append((w,v))
                    if verbose: print "Isolated vertex",(w,v)
                else:
                    for w in adjacent_twice_light_squares[v]:
                        semi_isolated_vertices.append((w,v))
                        if verbose: print "Semi-isolated vertex",(w,v)

                        
        # create the convex core as a square complex

        edges=set()
        vertices=set()
        
        # they are three kind of cells:
        # - squares: (w,v,a,b) where a and b are positive letters
        # - edges: (w,v,(a,0)) or (w,v,(b,1)) where a and b are positive letters
        # - vertices: (w,v)

        # where w is a path in G0 starting at v0, v is a vertex in G1
        # standing for the vertex of T1 at the end of t1(v), a is a
        # letter of A0 and b is a letter of A1.

        # Note that len(cell)-2 is its dimension

        for sq in heavy_squares:
            (e0,e1,e2,e3)=self.boundary(sq)
            edges.add(e0)
            edges.add(e1)
            edges.add((e3[0],e2[1],e0[2])) # we orient the edge for it to be labeled with a positive letter
            edges.add((e0[0],e0[1],e1[2])) # we orient the edge for it to be labeled with a positive letter

            # we now add the four corners of the square
            
            vertices.add((e0[0],e0[1]))
            vertices.add((e1[0],e1[1]))
            vertices.add((e2[0],e2[1]))
            vertices.add((e3[0],e3[1]))

        for e in isolated_edges:
            edges.add(e)
            vi,vt=self.boundary(e)
            vertices.update([vi,vt])

        for v in isolated_vertices:
            vertices.add(v)

        for v in semi_isolated_vertices:
            vertices.add(v)

        vertex_labels=list(vertices)
        vertex_labels.sort()

        if verbose: print "Vertices",vertex_labels
        # There are still isolated edges of the form (a,0) missing
        for a in A0.positive_letters():
            if not existing_edges[(a,0)]:
                if verbose: print "Looking for the isolated edge",(a,0)
                vi=G0.initial_vertex(a)
                vt=G0.terminal_vertex(a)
                u=G1.reduce_path(f(t0[vi]*Word([a])*G0.reverse_path(t0[vt])))
                first_start=True
                first_end=True
                for (w,v) in vertices:
                    if len(w)>0:
                        vc=G0.terminal_vertex(w[-1])
                    else:
                        vc=G0.initial_vertex(A0[0])
                    if vc==vi:
                        pfowv=self.path_from_origin((w,v),1) # path from the initial vertex of the edge to (w,v)
                        if first_start:
                            start_prefix=pfowv
                            first_start=False
                        else:
                            l=G1.common_prefix_length(start_prefix,pfowv)
                            if l<len(start_prefix):
                                start_prefix=start_prefix[:l]
                    if vc==vt:
                        pfttowv=G1.reduce_path(u*self.path_from_origin((w,v),1)) # path from the terminal vertex of the edge to (w,v)
                        if first_end:
                            end_prefix=pfttowv
                            first_end=False
                        else:
                            l=G1.common_prefix_length(end_prefix,pfttowv)
                            if l<len(end_prefix):
                                end_prefix=end_prefix[:l]
                if verbose: print "On side 1",(a,0),"is separated from self by",start_prefix,"and",end_prefix

                if len(start_prefix)>len(end_prefix):
                    prefix=start_prefix
                else:
                    prefix=end_prefix
                if len(prefix)==0:
                    e=(t0[G0.initial_vertex(a)],G1.initial_vertex(A1[0]),(a,0))
                    edges.add(e)
                    isolated_edges.append(e)
                    if verbose: print "Isolated edge:",e
                else:
                    v1=G1.terminal_vertex(prefix[-1])
                    u=G0.reduce_path(g(t1[v1]*G1.reverse_path(prefix))*t0[G0.initial_vertex(a)])
                    edges.add((u,v1,(a,0)))
                    isolated_edges.append((u,v1,(a,0)))
                    if verbose: print "Isolated edge:",(u,v1,(a,0))

        # We now number the vertices and change edges such that they are of the form [vi,vt,(a,side)]

        edges=list(edges)
        for i in xrange(len(edges)):
            e=edges[i]
            b=self.boundary(e)
            edges[i]=[bisect.bisect(vertex_labels,b[0])-1,bisect.bisect(vertex_labels,b[1])-1,e[2]]

        # Do not forget the isolated edges

        for i,e in enumerate(isolated_edges):
            b=self.boundary(e)
            isolated_edges[i]=[bisect.bisect(vertex_labels,b[0])-1,bisect.bisect(vertex_labels,b[1])-1,e[2]]
            
        # We change the heavy squares such that they are of the form [c1,c2,c3,c4,a,b]
            
        for i in xrange(len(heavy_squares)):
            sq=heavy_squares[i]
            b=self.boundary(sq)            
            sq=[bisect.bisect(vertex_labels,(b[j][0],b[j][1]))-1 for j in xrange(4)]+[sq[2],sq[3]]
            heavy_squares[i]=sq

        # We change the twice_light_squares in the same fashion

        for i in xrange(len(twice_light_squares)):
            sq=twice_light_squares[i]
            b=self.boundary(sq)
            c0=bisect.bisect(vertex_labels,(b[0][0],b[0][1]))-1
            c2=bisect.bisect(vertex_labels,(b[2][0],b[2][1]))-1
            c1=len(vertices)+2*i #These two vertices are not part of the convex-core
            c3=len(vertices)+2*i+1
            twice_light_squares[i]=[c0,c1,c2,c3,sq[2],sq[3]]
            
        # We now collapse squares and edges of length 0

        equivalent=range(len(vertices)+2*len(twice_light_squares))
        quotient=False
        if isinstance(G0,MetricGraph):
            i=0
            while i<len(edges):
                [vi,vt,(a,side)]=edges[i]
                if side==0 and G0.length(a)==0:
                    quotient=True
                    vii=equivalent[vi]
                    while vi!=vii:
                        vi=vii
                        vii=equivalent[vi]
                    vtt=equivalent[vt]
                    while vt!=vtt:
                        vt=vtt
                        vtt=equivalent[vt]
                    if vi<vt:
                        equivalent[vt]=vi
                    else:
                        equivalent[vi]=vt
                    edges.pop(i)
                else:
                    i+=1
            i=0
            while i<len(twice_light_squares):
                sq=twice_light_squares[i]
                if G0.length(sq[4])==0:
                    quotient=True
                    equivalent[sq[1]]=sq[0]
                    equivalent[sq[3]]=sq[2]
                    twice_light_squares.pop(i)
                    edges.append([sq[0],sq[2],(sq[5],1)])
                else:
                    i+=1

            i=0
            while i<len(heavy_squares):
                sq=heavy_squares[i]
                if G0.length(sq[4])==0:
                    quotient=True
                    heavy_squares.pop(i)
                else:
                    i+=1

            i=0
            while i<len(isolated_eges):
                e=isolated_edges[i]
                if e[2][1]==0 and G0.length(e[2][0])==0:
                    isolated_edges.pop(i)

        if isinstance(G1,MetricGraph):
            i=0
            while i<len(edges):
                [vi,vt,(a,side)]=edges[i]
                if side==1 and G1.length(a)==0:
                    quotient=True
                    vii=equivalent[vi]
                    while vi!=vii:
                        vi=vii
                        vii=equivalent[vi]
                    vtt=equivalent[vt]
                    while vt!=vtt:
                        vt=vtt
                        vtt=equivalent[vt]

                    if vi<vt:
                        equivalent[vt]=vi
                    else:
                        equivalent[vi]=vt
                    edges.pop(i)
                else:
                    i+=1
                    
            i=0
            while i<len(twice_light_squares):
                sq=twice_light_squares[i]
                if G1.length(sq[5])==0:
                    quotient=True
                    equivalent[sq[3]]=sq[0]
                    equivalent[sq[1]]=sq[2]
                    twice_light_squares.pop(i)
                    if A0.is_positive_letter(sq[4]):
                        edges.append([sq[0],sq[2],(sq[4],0)])
                    else:
                        edges.append([sq[2],sq[0],(A0.inverse_letter(sq[4]),0)])
                else:
                    i+=1

            i=0
            while i<len(heavy_squares):
                sq=heavy_squares[i]
                if G1.length(sq[5])==0:
                    heavy_squares.pop(i)
                else:
                    i+=1

            i=0
            while i<len(isolated_eges):
                e=isolated_edges[i]
                if e[2][1]==1 and G1.length(e[2][0])==0:
                    isolated_edges.pop(i)


        if quotient:
            for i in xrange(1,len(equivalent)):
                j=i
                k=equivalent[j]
                l=equivalent[k]
                while k>l:
                    equivalent[j]=l
                    j=k
                    k=l
                    l=equivalent[l]
                equivalent[i]=l

            vertices=[i for i in xrange(len(vertices)) if equivalent[i]==i]

            for e in edges:
                for i in xrange(2):
                    e[i]=equivalent[e[i]]

            for sq in heavy_squares:
                for i in xrange(4):
                    sq[i]=equivalent[sq[i]]

            for sq in twice_light_squares:
                for i in xrange(4):
                    sq[i]=equivalent[sq[i]]

        
            
                    
            
                
        
        self._squares=heavy_squares
        self._edges=edges
        if quotient:
            self._vertices=vertices
        else:
            self._vertices=range(len(vertices))
        self._twice_light_squares=twice_light_squares
        self._vertex_labels=vertex_labels

        self._isolated_edges=isolated_edges
        

    def _build_signed_ends(self,verbose=False):
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


        t0=self._t0
        t1=self._t1

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
            w=G0.reduce_path(g(f(G0.reverse_path(w)))*w)
            for b in image_a: # the image f(a) crosses the edge prefix.b
                pb=A1.to_positive_letter(b)
                u0=g(t1[G1.initial_vertex(pb)])
                if b==pb:
                    w0=G0.reduce_path(u0*w)
                    if len(w0)==0 or w0[-1]!=A0.inverse_letter(a):
                        signed_ends[pb].append((w0*Word([a]),'+'))
                    else:
                        signed_ends[pb].append((w0,'-'))
                w=G0.reduce_path(g.image(A1.inverse_letter(b))*w)
                if b!=pb:
                    w0=G0.reduce_path(u0*w)
                    if len(w0)==0 or w0[-1]!=A0.inverse_letter(a):
                        signed_ends[pb].append((w0*Word([a]),'-'))
                    else:
                        signed_ends[pb].append((w0,'+'))


        self._signed_ends=signed_ends

    def boundary(self,cell):
        """The boundary of a cell is the list of vertices bounding it. 

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
          labeling edges of G0 and G1:

                a
          v3 ------> v2
           ^         ^
           |         |
           |b        |b
           |         |
           |    a    |
          v0 ------>v1

        - edges: ``[v0,v1,(a,side)]`` where ``v0`` and ``v1`` are
          integers standing for vertices a is a label of the tree on
          ``side``.

        """
        if isinstance(cell,tuple):
            if len(cell)==4: # cell is a square
                w,v,a,b=cell
                ww,vv=self.boundary((w,v,(b,1)))[1]
                aa=self._G0.alphabet().inverse_letter(a)
                bb=self._G1.alphabet().inverse_letter(b)
                return [(w,v,(a,0)),(self._G0.reduce_path(w*Word([a])),v,(b,1)),(self._G0.reduce_path(ww*Word([a])),vv,(aa,0)),(ww,vv,(bb,1))]
            elif len(cell)==3: # cell is an edge
                (w,v,(a,i))=cell
                if i==0:
                    vv=v
                    ww=self._G0.reduce_path(w*Word([a]))
                else: # i=1
                    G0=self._G0
                    G1=self._G1
                    t1=self._t1
                    f10=self._f10
                    vv=G1.terminal_vertex(a)
                    aa=G1.alphabet().inverse_letter(a)
                    ww=G0.reduce_path(f10(t1[vv]*Word([aa])*G1.reverse_path(t1[v]))*w)
                return [(w,v),(ww,vv)]
        else: #the cell is a list of the form [v0,v1,v2,v3,v4,a,b]: square or [v0,v1,(a,side)]: edge
            if len(cell)==6:
                return cell[:4]
            else:
                return cell[:2]
            
        
    def path_from_origin(self,vertex,side,verbose=False):
        """Path from the origin of ``self`` to ``vertex`` on ``side``.

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

        - ``side``: 0 or 1

        EXAMPLES::

        sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")
        sage: phi=phi*phi
        sage: C=ConvexCore(phi)
        sage: C.path_from_origin(2,0)
        word: Bc
        
        sage: C.path_from_origin(('Bc',0),0)
        word: Bc

        sage: C.path_from_origin(('Bc',0),1)
        word: a
        

        """
        if not isinstance(vertex,tuple): # The vertex is an integer
            vertex=self._vertex_labels[vertex]
        
            
        if side==0:
            return vertex[0]
        else: #side==1
            w=vertex[0]
            if len(w)==0:
                return self._t1[vertex[1]]
            else:
                t0=self._t0
                G0=self._G0
                G1=self._G1
                t1=self._t1
                f01=self._f01
                return G1.reduce_path(f01(t0[G0.terminal_vertex(w[-1])]*G0.reverse_path(w))*t1[vertex[1]])

        
    def tree(self,side):
        """
        ``T0`` or ``T1`` (according to ``side``) where ``self`` is the
        convex core of the trees ``T0`` and ``T1``.

        """
        if side==0:
            return self._G0
        else:
            return self._G1

    def squares(self):
        """
        List of squares of ``self``.
        """
        return self._squares

    def twice_light_squares(self):
        """
        List of twice light squares of ``self``.
        """
        return self._twice_light_squares
    
    def edges(self):
        """
        List of edges of ``self``.
        """
        return self._edges


    def vertices(self):
        """
        List of vertices of ``self``.
        """
        return self._vertices

    def isolated_edges(self):
        """
        List of isolated edges
        """
        return self._isolated_edges

    def slice(self,a,side):
        """
        Slice of ``self`` for the edge ``a`` of the given ``side``.

        The slice is the tree whose vertices are edges labeled by
        ``(a,side)`` and with edges the squares with one side
        corresponding to ``(a,side)``.

        OUTPUT:

        A ``DiGraph``, edges are labeled by the corresponding
        square of ``self``,vertices by the corresponding edge.

        INPUT:

        If ``self`` is the core of the trees ``T0`` and ``T1`` and
        ``side==0`` then ``a`` is an edge of ``T0``. Conversely if
        ``side==1`` then ``a`` is an edge of ``T1``.

        EXAMPLES::
        
        sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")
        sage: phi=phi*phi
        sage: C=ConvexCore(phi)
        sage: print C.slice('c',0)
        Looped multi-digraph on 2 vertices

        """

        G=DiGraph(loops=True,multiedges=True)
        for sq in self.squares():
            if sq[4+side]==a:
                if side==0:
                    G.add_edge(((sq[0],sq[1],(a,0)),(sq[3],sq[2],(a,side)),sq[5]))
                else:
                    G.add_edge(((sq[0],sq[3],(a,1)),(sq[1],sq[2],(a,1)),sq[4]))
        return G


    def one_squeleton(self,side,augmented=False):
        """One squeleton of ``self`` on the ``side``

        INPUT:

        ``side`` is 0 or 1, standing for ``T0`` or ``T1``


        OUTPUT:

        A ``DiGraph`` edges are labeled by letters of the alphabet and
        vertices are labeled by the vertices of ``self``.

        """

        G=self.tree(side)
        A=G.alphabet()
        result=DiGraph(loops=True,multiedges=True)

        for e in self.edges():
            if e[2][1]==side:
                result.add_edge((e[0],e[1],e[2][0]))

        if augmented:
            for sq in self.twice_light_squares():
                if side==0:
                    a=sq[4]
                    if A.is_positive_letter(a):
                        result.add_edge((sq[0],sq[1],a))
                    else:
                        aa=A.inverse_letter(a)
                        result.add_edge((sq[1],sq[0],aa))
                else:
                    b=sq[5] # it is assumed that b is a positive letter
                    result.add_edge((sq[1],sq[2],b))
        
        return result

    def volume(self):
        """
        Volume of ``self``.

        If the trees are not metric trees then this is the simplicial
        volume: the number of squares in the 2-squeleton. 
        
        If the trees are metric trees, then this is the volume.
        """

        G0=self.tree(0)
        G1=self.tree(1)


        if isinstance(G0,MetricGraph) and isinstance(G1,MetricGraph): 
            result=0
            for  sq in self.squares():
                result+=G0.length(sq[4])*G1.length(sq[5])
            return result
        elif isinstance(G0,MetricGraph):
            result=0
            for sq in self.squares():
                result+=G0.length(sq[4])
            return result
        elif isinstance(G1,MetricGraph):
            result=0
            for sq in self.squares(): 
                result+=G1.length(sq[5])
            return result
        else:
            return len(self.squares())

    def rips_machine_holes(self,side=None,orientation=None,verbose=False):
        """
        The list of holes that can be digged by the Rips machine.

        A hole is a list ``[e,(b,i),right,left]`` where ``e`` is
        an edge on side ``1-i``, ``b`` a letter on the other side and
        ``right`` and ``left`` the lists of partial isometries on the
        right or the left of the hole.
        """

        T0=self.tree(0)
        T1=self.tree(1)

        A0=T0.alphabet()
        A1=T1.alphabet()

        squares=self.squares()

        boundary_squares=self.squares_of_the_boundary(verbose=verbose and verbose>1 and verbose-1) 

        if verbose:
            print "Squares not surrounded by four squares",boundary_squares


        if orientation is None:
            orientation=getattr(self,'_squares_orientation',None)

        if orientation is None: 
            orientation=self.squares_orientation()

                    
        point_of_domain=dict()
        for e in self.edges():
            point_of_domain[e[2]]=e[0]
            if e[2][1]==0:
                point_of_domain[(A0.inverse_letter(e[2][0]),0)]=e[1]
            else:
                point_of_domain[(A1.inverse_letter(e[2][0]),1)]=e[1]

        for sq in self.twice_light_squares():
            point_of_domain[(sq[4],0)]=sq[0]
            point_of_domain[(sq[5],1)]=sq[0]
            point_of_domain[(A0.inverse_letter(sq[4]),0)]=sq[2]
            point_of_domain[(A1.inverse_letter(sq[5]),0)]=sq[2]
            
                
        if verbose:
            print "Domains of the letters"
            print point_of_domain
                
        holes=[] # a hole is given by an edge in one of the two trees
                 # (v,w,(a,i)), a letter in the other alphabet and the
                 # list of partial isometries whose domain is on the
                 # same side of the hole as the starting point of the
                 # edge and the list of partial isometries on the
                 # other side.
    
        for (sqi,i) in boundary_squares:
            sq=squares[sqi]
            if side is None or i%2==side:
                if i==0:
                    e=(sq[0],sq[1],(sq[4],0))
                    b=(sq[5],1)
                elif i==1:
                    e=(sq[1],sq[2],(sq[5],1))
                    b=(A0.inverse_letter(sq[4]),0)
                elif i==2:
                    e=(sq[3],sq[2],(sq[4],0))
                    b=(A1.inverse_letter(sq[5]),1)
                elif i==3:
                    e=(sq[0],sq[3],(sq[5],1))
                    b=(sq[4],0)
                if orientation is not None and orientation[sqi]==-1:
                    e=(e[1],e[0],(self.tree(side=e[2][1]).alphabet().inverse_letter(e[2][0]),e[2][1]))
                if b[1]==0:
                    A=A0
                    T=T1
                else:
                    A=A1
                    T=T0
                p=T.reverse_path(self.path_from_origin(e[0],e[2][1]))
                start_letters=[]
                end_letters=[]
                for x in A:
                    if x!=b[0]:
                        px=T.reduce_path(p*self.path_from_origin(point_of_domain[(x,b[1])],e[2][1]))
                        if len(px)==0 or px[0]!=e[2][0]: # x is on the side of start
                            start_letters.append(x)
                        else:
                            end_letters.append(x)
                holes.append((e,b,start_letters,end_letters))

        return holes



    def rips_machine_moves(self,side=None,holes=None,orientation=None,verbose=False):
        r"""
        Return the list of possible moves of the Rips machine.

        A move is an automorphism of the free group. Assume that self
        is the convex core of an automorphism phi. Let psi be an
        automorphism given by ``self.rips_machine_moces(side=1)``,
        then ``ConvexCore(phi*psi)`` is obtained from ``self`` by a
        move of the Rips machine. On the other side: if ``psi`` is
        given by ``self.rips_machine_moces(side=0)``, then
        ``ConvexCore(psi.inverse()*phi)`` is given by a move of the
        Rips machine.

        INPUT:

        - `side` (default 0): side of Rips moves to find, either 0, 1
        or None for both sides.  
        
        OUPUT:

        - A list of free group automorphisms.

        """

        if holes is None:
            holes=self.rips_machine_holes(side=side,orientation=orientation,verbose=verbose and verbose>1 and verbose-1)

        if verbose:
            print "Holes:",holes

        result=[]        
        
        for e,b,start_letters,end_letters in holes:
            A=self.tree(side=b[1]).alphabet()

            hole_map=dict((a,Word([a])) for a in A.positive_letters())
                
            bb=A.inverse_letter(b[0])
            if bb in start_letters:
                for x in end_letters:
                    if A.is_positive_letter(x):
                        hole_map[x]=Word([bb])*hole_map[x]
                    else:
                        xx=A.inverse_letter(x)
                        hole_map[xx]=hole_map[xx]*Word([b[0]])
            else:
                for x in start_letters:
                    if A.is_positive_letter(x):
                        hole_map[x]=Word([bb])*hole_map[x]
                    else:
                        xx=A.inverse_letter(x)
                        hole_map[xx]=hole_map[xx]*Word([b[0]])
            result.append(hole_map)    
            
        return result
        
        
    def squares_orientation(self,orientation=1,verbose=False):
        """Assuming that ``self`` is an orientable surface square-complex,
        chose a coherent orientation of the squares.


        A coherent orientation is such that two squares sharing an
        edge are coherently oriented.  If there are more than one
        strongly connected component of squares then they get
        different numbers.

        Intended to be used by ``ConvexCore.plot_ideal_curve_diagram()``.

        INPUT:

        - ``orientation`` (default 1): the orientation of the first
          square of ``self``. It can be either 1 or -1.

        OUTPUT:
        
        A list of positive and negative numbers such that two adjacent
        squares are coherently oriented (same number).

        """

        squares=self.squares()
        
        if len(squares)==0:
            return []
        
        squares_orientation=[orientation]+[0 for i in xrange(1,len(squares))]

        todo=[0] # oriented squares with not yet oriented neighboors

        oriented=1 #number of oriented squares


        while oriented<len(squares):
            while len(todo)>0 and oriented<len(squares):
                i=todo.pop()
                sqi=squares[i]
                for j in xrange(1,len(squares)):
                    if squares_orientation[j]==0:
                        sqj=squares[j]
                        if sqi[4]==sqj[4] and ((sqi[0]==sqj[0] and sqi[1]==sqj[1]) or (sqi[3]==sqj[3] and sqi[2]==sqj[2])):
                            squares_orientation[j]=-squares_orientation[i]
                            todo.append(j)
                            oriented+=1
                        elif sqi[4]==sqj[4] and ((sqi[0]==sqj[3] and sqi[1]==sqj[2]) or (sqi[3]==sqj[0] and sqi[2]==sqj[1])):
                            squares_orientation[j]=squares_orientation[i]
                            todo.append(j)
                            oriented+=1
                        elif sqi[5]==sqj[5] and ((sqi[0]==sqj[0] and sqi[3]==sqj[3]) or (sqi[1]==sqj[1] and sqi[2]==sqj[2])):
                            squares_orientation[j]=-squares_orientation[i]
                            todo.append(j)
                            oriented+=1
                        elif sqi[5]==sqj[5] and ((sqi[0]==sqj[1] and sqi[3]==sqj[2]) or (sqi[1]==sqj[0] and sqi[2]==sqj[3])):
                            squares_orientation[j]=squares_orientation[i]
                            todo.append(j)
                            oriented+=1
            if oriented<len(squares): # there is more than one strongly connected component
                if verbose:
                    print "There is another strongly connected component"
                for i in xrange(1,len(squares)):
                    if squares_orientation[i]==0:
                        break
                todo.append(i)
                if orientation>0:
                    orientation+=1
                else:
                    orientation-=1
                squares_orientation[i]=orientation
                oriented+=1

        return squares_orientation
        
    def squares_of_the_boundary(self,verbose=False):
        """
        List of squares which are not surrounded by 4 squares.

        OUTPUT:

        A list of pairs (square,i) where square is a square and i is
        0,1,2 or 3 designating the edge of square which is not bounded
        by another square.
        """
        
        valence=dict(((e[0],e[1],e[2]),True) for e in self.edges())
        # valence[e]=True if the edge e has valence 0,
        # valence[e]=(i,j) if i is the unique square bounding e and e
        # is the j-th edge of i and False if there are at least two
        # squares bounding e.

        for i,sq in enumerate(self.squares()):
            if valence[(sq[0],sq[1],(sq[4],0))] is True:
                valence[(sq[0],sq[1],(sq[4],0))]=(i,0)
            else:
                valence[(sq[0],sq[1],(sq[4],0))]=False
                
            if valence[(sq[0],sq[3],(sq[5],1))] is True:
                valence[(sq[0],sq[3],(sq[5],1))]=(i,3)
            else:
                valence[(sq[0],sq[3],(sq[5],1))]=False
                
            if valence[(sq[1],sq[2],(sq[5],1))] is True:
                valence[(sq[1],sq[2],(sq[5],1))]=(i,1)
            else:
                valence[(sq[1],sq[2],(sq[5],1))]=False
                
            if valence[(sq[3],sq[2],(sq[4],0))] is True:
                valence[(sq[3],sq[2],(sq[4],0))]=(i,2)
            else:
                valence[(sq[3],sq[2],(sq[4],0))]=False
                    
        boundary_squares=[s for e,s in valence.iteritems() if ((s is not True) and (s is not False))]
         
        return  boundary_squares

    def surface_boundary(self,orientation=None,verbose=False):
        """List of edges in the boundary of the square complex.

        Attended to be used by
        `ConvexCore.plot_ideal_curve_diagram()`.

        OUTPOUT:

        A list of triples (v,w,(a,i,j)) where v and w are vertices a
        is a letter of the alphabet of the side i and j is an
        orientation: it can be 0 meaning that the edge is oriented in
        this direction or a non-zero number specifying the orientation
        of the square bounding the edge.

        """

        if orientation is None:
            orientation=getattr(self,'_squares_orientation',None)

        if orientation is None: 
            orientation=self.squares_orientation()
        
        squares=self.squares()
        
        boundary_squares=self.squares_of_the_boundary(verbose=verbose and verbose>1 and verbose-1)

        result=[]

        
        for (i,j) in boundary_squares:
            sq=squares[i]
            if j==0 or j==1:
                result.append((sq[j],sq[(j+1)%4],(sq[4+(j%2)],j%2,orientation[i])))
                result.append((sq[(j+1)%4],sq[j],(self.tree(side=j).alphabet().inverse_letter(sq[4+(j%2)]),j%2,-orientation[i])))
            else:
                result.append((sq[(j+1)%4],sq[j],(sq[4+(j%2)],j%2,-orientation[i])))
                result.append((sq[j],sq[(j+1)%4],(self.tree(side=j-2).alphabet().inverse_letter(sq[4+(j%2)]),j%2,orientation[i])))
            
            
        for e in self.isolated_edges():
            result.append((e[0],e[1],(e[2][0],e[2][1],0)))
            result.append((e[1],e[0],(self.tree(side=e[2][1]).alphabet().inverse_letter(e[2][0]),e[2][1],0)))

        for sq in self.twice_light_squares():
            result.append((sq[0],sq[1],(sq[4],0,0)))
            result.append((sq[1],sq[2],(sq[5],1,0)))
            result.append((sq[1],sq[0],(self.tree(side=0).alphabet().inverse_letter(sq[4]),0,0)))
            result.append((sq[2],sq[1],(self.tree(side=1).alphabet().inverse_letter(sq[5]),1,0)))

        return result
                
    def plot_ideal_curve_diagram(self,radius=1, orientation=1, cyclic_order_0=None, cyclic_order_1=None,verbose=False):

        """Plot the set of ideal curves on the surface S=S(g,1) of genus g with
        one puncture.

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

        - ``radius``: (default 1) the radius of the regular 2N-gone
          which is the fondamental domain of the surface.

        -``cyclic_order_0``: (default None) List of edges outgoing
         from the sole vertex of T0 ordered according to the embedding
         in the surface. A typical value in rank 4, compatible with
         the definition of ``FreeGroup.surface_dehn_twist()`` is :
         ['A','B','a','C','D','c','d','b']

        -``cyclic_order_1``: (default None) List of edges outgoing
         from the sole vertex of T1 ordered according to the embedding
         in the surface.

        EXAMPLES::
        
        sage: F=FreeGroup(4)
        sage: phi=mul([F.surface_dehn_twist(i) for i in [2,1,1,4]])
        sage: C=ConvexCore(phi)
        sage: C.plot_ideal_curve_diagram(cyclic_order_0=['A','B','a','C','D','c','d','b'])

        """

        from sage.plot.line import Line
        from sage.plot.arrow import Arrow
        
        T0=self.tree(0)
        T1=self.tree(1)
        A0=T0.alphabet()
        N=len(A0)
        A1=T1.alphabet()

        # Let ``self`` be the convex core of trees T0 and T1. T0 and
        # T1 need to be roses. The trees T0 and T1 may be given as
        # embedded inside the surface. In this case the edges outgoing
        # from the sole vertex are cyclically ordered.

        if len(T0.vertices())!=1:
            raise ValueError('The tree on side 0 must be a rose')
        if len(T1.vertices())!=1:
            raise ValueError('The tree on side 1 must be a rose')
            
        
        if cyclic_order_0 is None:
            cyclic_order_0=getattr(T0,'cyclic_order',None)
        if cyclic_order_1 is None:
            cyclic_order_1=getattr(T1,'cyclic_order',None)

        if verbose:
            if cyclic_order_0 is not None:
                print "The tree on side 0 is embedded in the surface:",cyclic_order_0
            else:
                print "The tree on side 0 is not embedded in the surface, we will try to guess an embedding"
            if cyclic_order_1 is not None:
                print "The tree on side 1 is embedded in the surface:",cyclic_order_1
            else:
                print "The tree on side 1 is not embedded in the surface, we will try to guess an embedding"
            
        squares=self.squares()

        # Coherent orientation of the squares
            

        orientation=self.squares_orientation(orientation=orientation,verbose=verbose and verbose>1 and verbose-1)
            
        if verbose:
            print "Orientation of the squares:"
            if verbose>1:
                for i,sq in enumerate(squares):
                    print i,":",sq,":",orientation[i] 

        boundary=self.surface_boundary(orientation=orientation,verbose=verbose and verbose>1 and verbose-1)


        if verbose:
            print "Edges of the boundary:"
            print boundary
        
        # The boundary of the surface is an Eulerian circuit in the surface_boundary_graph
        
        eulerian_circuits=[]

	boundary_length=2*(self.tree(side=0).alphabet().cardinality()+self.tree(side=1).alphabet().cardinality())

        next=[(boundary[0],0)]
        if boundary[0][2][2]!=0:
            next.append((boundary[1],0))

        if verbose:
            print "Looking for an eulerian circuit in the boundary"

        while len(next)>0:

            e,current=next.pop()

            if verbose:
                print e,current
            
            for i in xrange(current+1,len(boundary)):
                if boundary[i]==e:
                    boundary[i],boundary[current]=boundary[current],boundary[i]
                    # now the boundary is the beginning of an eulerian
                    # circuit up to current
                    break

            # We check that the boundary up to current is acceptable

            acceptable=True

            # First, we check that two edges bounding a strongly
            # connected component of squares share the same
            # orientation
            
            oriented=set()
            for i in xrange(current+1):
                e=boundary[i]
                if e[2][2]!=0 and -e[2][2] in oriented: # edges with orientation 0 are isolated edges
                    acceptable=False
                    if verbose:
                        print "The current boundary does not respect orientation",e[2][2]
                    break
                else:
                    oriented.add(e[2][2])

            if not acceptable:
                continue
            
            # Next we check that this is compatible with the given
            # cyclic order

            if cyclic_order_0 is not None:                
                i=0
                j0=None
                while i<current+1 and boundary[i][2][1]!=0: 
                    i+=1
                if i<current+1:
                    j0=0
                    while j0<len(cyclic_order_0) and cyclic_order_0[j0]!=boundary[i][2][0]:
                        j0+=1
                
                while i<current:
                    i+=1
                    while i<current+1 and boundary[i][2][1]!=0:
                        i+=1
                    if i<current+1:
                        j0+=1
                        if j0==len(cyclic_order_0):
                            j0=0
                        if boundary[i][2][0]!=cyclic_order_0[j0]:
                            acceptable=False
                            if verbose:
                                print "The current boundary does not respect the given cyclic order on side 0"
                            break

            if not acceptable:
                continue
            
            if cyclic_order_1 is not None:                
                i=0
                j1=None
                while i<current+1 and boundary[i][2][1]!=1:
                    i+=1
                if i<current+1:
                    j1=0
                    while j1<len(cyclic_order_1) and cyclic_order_1[j1]!=boundary[i][2][0]:
                        j1+=1
                while i<current:
                    i+=1
                    while i<current+1 and boundary[i][2][1]!=1:
                        i+=1
                    if i<current+1:
                        j1+=1
                        if j1==len(cyclic_order_1):
                            j1=0
                        if boundary[i][2][0]!=cyclic_order_1[j1]:
                            acceptable=False
                            if verbose:
                                print "The current boundary does not respect the given cyclic order on side 1"

                            break

            if not acceptable:
                continue

            if current+1==boundary_length:
                eulerian_circuits.append(boundary[:current+1])    
            
            for i in xrange(current+1,len(boundary)):
                e=boundary[i]
                if e[0]!=boundary[current][1] or (e[2][2]!=0 and -e[2][2] in oriented):
                    continue
                if e[2][1]==0 and (cyclic_order_0 is not None) and (j0 is not None):
                    jj0=j0+1
                    if jj0==len(cyclic_order_0):
                        jj0=0
                    if e[2][0]!=cyclic_order_0[jj0]:
                        continue
                elif e[2][1]==1 and (cyclic_order_1 is not None) and (j1 is not None):
                    jj1=j1+1
                    if jj1==len(cyclic_order_1):
                        jj1=0
                    if e[2][0]!=cyclic_order_1[jj1]:
                        continue

                next.append((e,current+1))
                
                            

                
        if verbose:
            print "Possible boundaries:",eulerian_circuits
        
        if len(eulerian_circuits)>1:
            print "There is an ambiguity on the choice of the boundary of the surface."
            print "Specify using optionnal argument cyclic_order_0 and cyclic_order_1."
            print "Possible choices:"
            for cyclic_order in eulerian_circuits:
                print cyclic_order
            print "The first one is chosen"    
        elif len(eulerian_circuits)==0:
            print "There are no eulerian circuit in the boundary compatible with the given cyclic orders."
            print "Probably changing the orientation will solve this problem"
            return False
        
        cyclic_order=eulerian_circuits[0]

        # Now we can fix the orientation of the squares according to
        # the chosen boundary

        direct_orientation=set(e[2][2] for e in cyclic_order if e[2][2]!=0)
        
        for i in xrange(len(self.squares())):
            if orientation[i] in direct_orientation:
                orientation[i]=-1
            else:
                orientation[i]=1
        

        if verbose:
            print "Orientation of the squares coherent with the choice of the boundary"
            print orientation

        self._squares_orientation=orientation

        # We put the edges in the fundamental domain
                    
        initial_vertex=dict()
        terminal_vertex=dict()

        for a in A0.positive_letters():
            aa=A0.inverse_letter(a)
            slicea=[i for i in xrange(len(squares)) if squares[i][4]==a]
            size=len(slicea)+1

            if size==1:
                continue

            # sort the edges of the slice
            i=1
            sqi=slicea[0]
            sq=squares[sqi]
            if orientation[sqi]==1:
                start0=(sq[0],sq[1])
                endi=(sq[3],sq[2])
            else:
                start0=(sq[3],sq[2])
                endi=(sq[0],sq[1])

            while i<len(slicea):
                j=i
                while j<len(slicea):
                    sqjj=slicea[j]
                    sqj=squares[sqjj]
                    if orientation[sqjj]==1:
                        startj=(sqj[0],sqj[1])
                        endj=(sqj[3],sqj[2])
                    else:
                        startj=(sqj[3],sqj[2])
                        endj=(sqj[0],sqj[1])
                    
                    if endi==startj: # next(es[i-1])==es[j]:
                        slicea[j],slicea[i]=slicea[i],slicea[j]
                        i+=1
                        endi=endj
                        if i<j:
                            j=j-1
                    elif endj==start0: #next(es[j])==es[0]:
                        slicea=[slicea[j]]+slicea[:j]+slicea[j+1:]
                        i+=1
                        start0=startj
                        if i<j:
                            j=j-1
                    j+=1

            if verbose:
                print "Slice of", a,":",slicea       

            # put a curve for each edge of the slice
            for i,sqi in enumerate(slicea):
                sq=squares[sqi]
                if orientation[sqi]==1:
                    initial_vertex[(sq[0],sq[3],sq[5])]=(a,(i+1.0)/size)
                    terminal_vertex[(sq[1],sq[2],sq[5])]=(aa,(size-i-1.0)/size)
                else:
                    terminal_vertex[(sq[0],sq[3],sq[5])]=(a,(i+1.0)/size)
                    initial_vertex[(sq[1],sq[2],sq[5])]=(aa,(size-i-1.0)/size)


        # We compute the regular 2N-gone that is the foundamental domain
        # of the surface on side 0

        i=0
        while cyclic_order[i][2][1]==1:
            i+=1


        a=A0.inverse_letter(cyclic_order[i][2][0])
        polygon_side_0=[a]

        for j in xrange(2*N-1):
            k=0
            while cyclic_order[k][2][1]==1 or cyclic_order[k][2][0]!=a:
                k+=1
            k-=1
            while cyclic_order[k][2][1]==1:
                k-=1
                if k==0:
                    k=boundary_length-1
            a=A0.inverse_letter(cyclic_order[k][2][0])
            polygon_side_0.append(a)


        if verbose:
            print "Polygon bounding the fundamental domain of the surface:",polygon_side_0

        i=0
        while polygon_side_0[i]!=A0[0]:
            i+=1
        polygon_side_0=polygon_side_0[i:]+polygon_side_0[:i]
            
            
        g=Graphics()

        boundary_initial_vertex=dict()
        boundary_terminal_vertex=dict()

        for i,a in enumerate(polygon_side_0):
            boundary_initial_vertex[a]=(RR(radius*cos(i*pi/N)),RR(radius*sin(i*pi/N)))
            boundary_terminal_vertex[a]=(RR(radius*cos((i+1)*pi/N)),RR(radius*sin((i+1)*pi/N)))


        # Regular polygon
        text_decalage=1.05
        for a in polygon_side_0:
            x,y=boundary_initial_vertex[a]
            xx,yy=boundary_terminal_vertex[a]
            g+=line([(x,y),(xx,yy)],alpha=1,thickness=2,hue=5.0/6)
            g+=text(a,((x+xx)/2*text_decalage**2,(y+yy)/2*text_decalage**2),hue=5.0/6)
 

        for e in initial_vertex:
            a,p=initial_vertex[e]
            b=e[2]
            x=boundary_initial_vertex[a][0]+p*(boundary_terminal_vertex[a][0]-boundary_initial_vertex[a][0])
            y=boundary_initial_vertex[a][1]+p*(boundary_terminal_vertex[a][1]-boundary_initial_vertex[a][1])
            if e in terminal_vertex:
                aa,pp=terminal_vertex[e]
            else: # the end of e is at the singularity
                i=0
                j=0
                while cyclic_order[i][2][1]==0 or cyclic_order[i][2][0]!=b:
                    if cyclic_order[i][2][1]==0:
                        j=i
                    i+=1
                    
                if i==0:
                    j=len(cyclic_order)-1
                    while cyclic_order[j][2][1]==1:
                        j-=1
                aa=A0.inverse_letter(cyclic_order[j][2][0])
                pp=0

            xx=boundary_initial_vertex[aa][0]+pp*(boundary_terminal_vertex[aa][0]-boundary_initial_vertex[aa][0])
            yy=boundary_initial_vertex[aa][1]+pp*(boundary_terminal_vertex[aa][1]-boundary_initial_vertex[aa][1])

            if pp==0:
                g+=text(b,(text_decalage*x,text_decalage*y),hue=RR(A1.rank(b))/N)

            g+=line([(x,y),(xx,yy)],alpha=1,thickness=2,hue=RR(A1.rank(b))/N)
            
        for e in terminal_vertex:
            if e not in initial_vertex: # the initial vertex of e is the singularity
                aa,pp=terminal_vertex[e]
                xx=boundary_initial_vertex[aa][0]+pp*(boundary_terminal_vertex[aa][0]-boundary_initial_vertex[aa][0])
                yy=boundary_initial_vertex[aa][1]+pp*(boundary_terminal_vertex[aa][1]-boundary_initial_vertex[aa][1])
                b=A1.inverse_letter(e[2])
                i=0
                j=0
                while cyclic_order[i][2][1]==0 or cyclic_order[i][2][0]!=b:
                    if cyclic_order[i][2][1]==0:
                         j=i
                    i+=1
                    
                if i==0:
                    j=len(cyclic_order)-1
                    while cyclic_order[j][2][1]==1:
                        j-=1
                a=A0.inverse_letter(cyclic_order[j][2][0])
                p=0
                x=boundary_initial_vertex[a][0]+p*(boundary_terminal_vertex[a][0]-boundary_initial_vertex[a][0])
                y=boundary_initial_vertex[a][1]+p*(boundary_terminal_vertex[a][1]-boundary_initial_vertex[a][1])
                
                g+=line([(x,y),(xx,yy)],alpha=1,thickness=2,hue=RR(A1.rank(b))/N)

        
        for e in self.isolated_edges():
            if e[2][1]==1:
                #The end of e is at the singularity
                b=e[2][0]
                i=0
                j=0
                while cyclic_order[i][2][1]==0 or cyclic_order[i][2][0]!=b:
                    if cyclic_order[i][2][1]==0:
                        j=i
                    i+=1
                    
                if i==0:
                    j=len(cyclic_order)-1
                    while cyclic_order[j][2][1]==1:
                        j-=1
                aa=A0.inverse_letter(cyclic_order[j][2][0])
                pp=0
                xx=boundary_initial_vertex[aa][0]+pp*(boundary_terminal_vertex[aa][0]-boundary_initial_vertex[aa][0])
                yy=boundary_initial_vertex[aa][1]+pp*(boundary_terminal_vertex[aa][1]-boundary_initial_vertex[aa][1])

                #The start of e is also at the singularity
                
                b=A1.inverse_letter(b)
                i=0
                j=0
                while cyclic_order[i][2][1]==0 or cyclic_order[i][2][0]!=b:
                    if cyclic_order[i][2][1]==0:
                         j=i
                    i+=1
                    
                if i==0:
                    j=len(cyclic_order)-1
                    while cyclic_order[j][2][1]==1:
                        j-=1
                a=A0.inverse_letter(cyclic_order[j][2][0])
                p=0
                x=boundary_initial_vertex[a][0]+p*(boundary_terminal_vertex[a][0]-boundary_initial_vertex[a][0])
                y=boundary_initial_vertex[a][1]+p*(boundary_terminal_vertex[a][1]-boundary_initial_vertex[a][1])

                g+=line([(x,y),(xx,yy)],alpha=1,thickness=2,hue=RR(A1.rank(b))/N)

            
        g.axes(False)

        return g

    def plot_punctured_disc_ideal_curves(self,verbose=False):
        pass


        

        
        
