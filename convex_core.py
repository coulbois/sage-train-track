#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

# from inverse_graph import GraphWithInverses
# from core import Core
# from sage.combinat.words.word import Word
# from inverse_graph import MetricGraph


class ConvexCore():
    """
    Guirardel's Convex core of two simplicial trees with an action of
    a free group.

    Let T1 and T2 be trees with actions of the free group FN. G1=T1/FN
    and G2=T2/FN are MarkedGraph or MarkedMetricGraph.

    A ConvexCore is a CW-complex of dimension 2. 2-cells are
    squares. 1 cells are edges labeled by edges of G1 or G2. A square
    is of the form

          e
        ----->
       |      |
       |      |
     f |      | f
       |      |
       v      v
        ----->
          e

    where e is an edge of G1 and f an edge of G2.

    ConvexCore(phi): where phi is an automorphism of the free group
    F. The convex core of the Cayley tree TA of the free group F with
    respect to its alphabet A, and of the tree TA.Phi, where Phi is
    the outer class of phi.

    ConvexCore(G1,G2): where G1 and G2 are two marked graphs (or two
    marked metric graphs): The convex core of the universal covers T1
    and T2 of G1 and G2 respectively. Edges of length 0 are quotient
    out.

    ConvexCore(f): where f is a homotopy equivalence between graphs G1 and G2:
    The convex core of the universal covers T1 and T2 of G1 and G2,
    with the fundamental group F of G1 acting on G2 through f. Edges
    of length 0 are quotient out.

    TODO:

    This uses the slice construction of Core and thus does not detect
    edges which do not bound a square.

    WARNING:

    The one squeleton may fail to be connected due to absence of some
    isolated edges

    """

    def __init__(self,*args):
        if len(args)==2: #ConvexCore(G,H)
            G=args[0]
            H=args[1]
            f=G.difference_of_marking(H).tighten()
            g=f.inverse()
            fe=f.edge_map()
            ge=g.edge_map()
            #CC=Core(H,G,g.edge_map(),f.edge_map())
        elif len(args)==1:
            if isinstance(args[0],GraphMap): #ConvexCore(f)
                G=f.domain()
                H=f.codomain()
                f=args[0]
                g=f.inverse()
                fe=f.edge_map()
                ge=g.edge_map()
                #CC=Core(f.codomain(),f.domain(),g.edge_map(),f.edge_map())
            elif isinstance(args[0],FreeGroupAutomorphism): # ConvexCore(phi)
                phi=args[0]
                A=phi.domain().alphabet()
                G=GraphWithInverses.rose_graph(A)
                H=GraphWithInverses.rose_graph(A)
                psi=phi.inverse()
                f=fe=phi
                g=ge=psi
                #CC=Core(G,H,psi,phi)
        elif len(args)==4: #ConvexCore(G,H,f,g)
            (G,H,fe,ge)=args
            f=fe
            g=ge

        self._T0=G
        self._T1=H

        C=Core(G,H,fe,ge)

        A=G.alphabet()
        B=H.alphabet()

        two_cells=[]

        for a in A.positive_letters():
            slice_a=C.core_slice(a)
            for e in slice_a.edges():
                if B.is_positive_letter(e[2]):
                    two_cells.append((Word(e[0]),a,e[2]))
                else:
                    two_cells.append((Word(e[1]),a,B.inverse_letter(e[2])))

        one_cells_G=set()
        one_cells_H=set()
        two_cell_boundary=dict()
        zero_cells=set()
        one_cell_G_boundary=dict()
        one_cell_H_boundary=dict()


        for c in two_cells:
            v=c[0]
            a=c[1]
            b=c[2]
            vb=H.reduce_path(v*Word([b]))
            Av=H.reduce_path(f.image(A.inverse_letter(c[1]))*c[0])
            one_cells_H.add((v,b))
            one_cells_H.add((Av,b))
            one_cells_G.add((v,a))
            one_cells_G.add((vb,a))
            two_cell_boundary[c]=(((v,a),(vb,a),(v,b),(Av,b)))
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
        numbered_two_cells=[]

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

        


        

        
        
