#*****************************************************************************
#       Copyright (C) 2013 Matt Clay and Thierry Coulbois
#       <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from convex_core import ConvexCore


class IdealCurveDiagram(ConvexCore):      
    """
    Convex core of two trees that are transverse to ideal curves on a pointed surface.

    """
    
    

        
    def squares_orientation(self,orientation=1,verbose=False):
        """Assuming that ``self`` is an orientable surface square-complex,
        chose a coherent orientation of the squares.


        A coherent orientation is such that two squares sharing an
        edge are coherently oriented.  If there are more than one
        strongly connected component of squares then they get
        different numbers.

        Intended to be used by ``IdealCurveDiagram.plot()``.

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
                
    def plot(self,radius=1, orientation=1, cyclic_order_0=None, cyclic_order_1=None,verbose=False):

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

        from sage.plot.graphics import Graphics
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


            # If there are no given cyclic orders we check that on
            # both side there is only one connected component.

            if (cyclic_order_0 is None) and (cyclic_order_1 is None):
                tmp_cyclic_0=[boundary[i][2][0] for i in xrange(current+1) if boundary[i][2][1]==0] 
                i=0
                if len(tmp_cyclic_0)<2*len(A0):
                    while i<len(tmp_cyclic_0):
                        j=i
                        done=False
                        while True: 
                            aa=A0.inverse_letter(tmp_cyclic_0[j])
                            j=0
                            while j<len(tmp_cyclic_0) and tmp_cyclic_0[j]!=aa:
                                j+=1
                            if j==len(tmp_cyclic_0) or j==0:
                                i+=1
                                break
                            j-=1
                            if i==j:
                                acceptable=False
                                if verbose:
                                    print "There is more than one boundary component on side 0"
                                    print "Cyclic order on side 0:",tmp_cyclic_0
                                i=len(tmp_cyclic_0)
                                break

                if not acceptable:
                    continue


                tmp_cyclic_1=[boundary[i][2][0] for i in xrange(current+1) if boundary[i][2][1]==1] 
                i=0
                if len(tmp_cyclic_1)<2*len(A1):
                    while i<len(tmp_cyclic_1):
                        j=i
                        done=False
                        while True: 
                            aa=A1.inverse_letter(tmp_cyclic_1[j])
                            j=0
                            while j<len(tmp_cyclic_1) and tmp_cyclic_1[j]!=aa:
                                j+=1
                            if j==len(tmp_cyclic_1) or j==0:
                                i+=1
                                break
                            j-=1
                            if i==j:
                                acceptable=False
                                if verbose:
                                    print "There is more than one boundary component on side 1"
                                    print "Cyclic order on side 1:",tmp_cyclic_1
                                i=len(tmp_cyclic_1)
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
                print "side 0:",[e[2][0] for e in cyclic_order if e[2][1]==0]
                print "side 1:",[e[2][0] for e in cyclic_order if e[2][1]==1]
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
                    
                if j==0 and cyclic_order[j][2][1]==1:
                    j=len(cyclic_order)-1
                    while cyclic_order[j][2][1]==1:
                        j-=1
                aa=A0.inverse_letter(cyclic_order[j][2][0])
                pp=0

            xx=boundary_initial_vertex[aa][0]+pp*(boundary_terminal_vertex[aa][0]-boundary_initial_vertex[aa][0])
            yy=boundary_initial_vertex[aa][1]+pp*(boundary_terminal_vertex[aa][1]-boundary_initial_vertex[aa][1])

            g+=line([(x,y),(xx,yy)],alpha=1,thickness=2,hue=RR(A1.rank(b))/N)
            
        for e in terminal_vertex:
            if e not in initial_vertex: # the initial vertex of e is the singularity
                aa,pp=terminal_vertex[e]
                xx=boundary_initial_vertex[aa][0]+pp*(boundary_terminal_vertex[aa][0]-boundary_initial_vertex[aa][0])
                yy=boundary_initial_vertex[aa][1]+pp*(boundary_terminal_vertex[aa][1]-boundary_initial_vertex[aa][1])
                b=A1.inverse_letter(e[2][0])
                i=0
                j=0
                while cyclic_order[i][2][1]==0 or cyclic_order[i][2][0]!=b:
                    if cyclic_order[i][2][1]==0:
                         j=i
                    i+=1
                    
                if j==0 and cyclic_order[j][2][1]==1:
                    j=len(cyclic_order)-1
                    while cyclic_order[j][2][1]==1:
                        j-=1
                a=A0.inverse_letter(cyclic_order[j][2][0])
                x=boundary_initial_vertex[a][0]
                y=boundary_initial_vertex[a][1]
                
                g+=line([(x,y),(xx,yy)],alpha=1,thickness=2,hue=RR(A1.rank(b))/N)

                g+=text(e[2][0],(text_decalage*xx,text_decalage*yy),hue=RR(A1.rank(b))/N)

        
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
                    
                if j==0 and cyclic_order[j][2][1]==1:
                    j=len(cyclic_order)-1
                    while cyclic_order[j][2][1]==1:
                        j-=1
                a=A0.inverse_letter(cyclic_order[j][2][0])
                x=boundary_initial_vertex[a][0]
                y=boundary_initial_vertex[a][1]

                #The start of e is also at the singularity 
                bb=A1.inverse_letter(b)
                i=0
                j=0
                while cyclic_order[i][2][1]==0 or cyclic_order[i][2][0]!=bb:
                    if cyclic_order[i][2][1]==0:
                        j=i
                    i+=1
                    
                if j==0 and cyclic_order[j][2][1]==1:
                    j=len(cyclic_order)-1
                    while cyclic_order[j][2][1]==1:
                        j-=1
                aa=A0.inverse_letter(cyclic_order[j][2][0])


                xx=boundary_initial_vertex[aa][0]
                yy=boundary_initial_vertex[aa][1]

                
                g+=line([(x,y),(xx,yy)],alpha=1,thickness=2,hue=RR(A1.rank(b))/N)

                g+=text(b,(text_decalage*x,text_decalage*y),hue=RR(A1.rank(b))/N)

        for sq in self.twice_light_squares():
            b=A1.to_positive_letter(sq[5])
            #The end of b is at the singularity
            i=0
            j=0
            while cyclic_order[i][2][1]==0 or cyclic_order[i][2][0]!=b:
                if cyclic_order[i][2][1]==0:
                     j=i
                i+=1

            if j==0 and cyclic_order[j][2][1]==1:
                j=len(cyclic_order)-1
                while cyclic_order[j][2][1]==1:
                    j-=1
            a=A0.inverse_letter(cyclic_order[j][2][0])
            x=boundary_initial_vertex[a][0]
            y=boundary_initial_vertex[a][1]

            #The start of b is also at the singularity 
            bb=A1.inverse_letter(b)
            i=0
            j=0
            while cyclic_order[i][2][1]==0 or cyclic_order[i][2][0]!=bb:
                if cyclic_order[i][2][1]==0:
                    j=i
                i+=1

            if j==0 and cyclic_order[j][2][1]==1:
                j=len(cyclic_order)-1
                while cyclic_order[j][2][1]==1:
                    j-=1
            aa=A0.inverse_letter(cyclic_order[j][2][0])


            xx=boundary_initial_vertex[aa][0]
            yy=boundary_initial_vertex[aa][1]


            g+=line([(x,y),(xx,yy)],alpha=1,thickness=2,hue=RR(A1.rank(b))/N)

            g+=text(b,(text_decalage*x,text_decalage*y),hue=RR(A1.rank(b))/N)


        g.axes(False)

        return g

    def plot_punctured_disc_ideal_curves(self,verbose=False):
        """Plot a disc with punctures and ideal curves with ``self`` as dual graph.

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

        """
        

        from sage.plot.graphics import Graphics
        from sage.plot.line import Line
        from sage.plot.arrow import Arrow
        
        T0=self.tree(0)
        T1=self.tree(1)
        A0=T0.alphabet()
        N=len(A0)

        # Coherent orientation of the squares
            
        orientation=self.squares_orientation(orientation=orientation,verbose=verbose and verbose>1 and verbose-1)

        if verbose:
            print "Orientation of the squares:"
            if verbose>1:
                for i,sq in enumerate(squares):
                    print i,":",sq,":",orientation[i] 

        # Edges of the boundary
                    
        boundary=self.surface_boundary(orientation=orientation,verbose=verbose and verbose>1 and verbose-1)

        if verbose:
            print "Edges of the boundary:"
            print boundary
