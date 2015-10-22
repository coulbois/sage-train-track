#*****************************************************************************
#       Copyright (C) 2015 Thierry Coulbois
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

class ConvexCoreWithRipsMachine(ConvexCore):

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
            orientation=self.squares_orientation(verbose=verbose and verbose>1 and verbose-1)

                    
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
            point_of_domain[(A1.inverse_letter(sq[5]),1)]=sq[2]
            
                
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
                    e=(sq[2],sq[3],(A0.inverse_letter(sq[4]),0))
                    b=(A1.inverse_letter(sq[5]),1)
                elif i==3:
                    e=(sq[3],sq[0],(A1.inverse_letter(sq[5]),1))
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

        result=[]        
        
        for i,hole in enumerate(holes):
            e,b,start_letters,end_letters=hole

            A=self.tree(side=b[1]).alphabet()

            hole_map=dict((a,Word([a])) for a in A.positive_letters())
                
            bb=A.inverse_letter(b[0])
            if bb in start_letters:
                if verbose:
                    print i,":",hole
                    print "surgery:",e[2],",",(bb,b[1])
                for x in end_letters:
                    if A.is_positive_letter(x):
                        hole_map[x]=Word([bb])*hole_map[x]
                    else:
                        xx=A.inverse_letter(x)
                        hole_map[xx]=hole_map[xx]*Word([b[0]])
            else:
                if verbose:
                    print i,":",hole
                    print "surgery:",e[2],",",b
                for x in start_letters:
                    if A.is_positive_letter(x):
                        hole_map[x]=Word([bb])*hole_map[x]
                    else:
                        xx=A.inverse_letter(x)
                        hole_map[xx]=hole_map[xx]*Word([b[0]])
            result.append(hole_map)    
            
        return result

    def unicorn_surgery_step(self,side=1,orientation=dict(),permutation=dict(),force_surgery=None,verbose=False):
        """Looks for a possible symmetric surgery on ``self``.

        First look for the list of possible holes. Then keep only
        those compatible with orientation and permutation.

        """
        
        A0=self.tree(side=0).alphabet()
        A1=self.tree(side=1).alphabet()

        T1=self.tree(side=1)
        
        phi=self._f01
        C=self

        holes=C.rips_machine_holes(side=side)

        # Adding isolated edges and exceptional surgeries

        if len(self.isolated_edges())>0:
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
                point_of_domain[(A1.inverse_letter(sq[5]),1)]=sq[2]

            
        for e in self.isolated_edges():
            if e[2][1]==side:
                if verbose:
                    print "Isolated edge:",e,"Corresponding to holes:"
                start_letters=[]
                end_letters=[]
                p=T1.reverse_path(self.path_from_origin(e[0],side))
                for b in A0:
                    px=T1.reduce_path(p*self.path_from_origin(point_of_domain[(b,0)],side))
                    if len(px)==0 or px[0]!=e[2][0]:
                        start_letters.append(b)
                    else:
                        end_letters.append(b)
                ee=(e[1],e[0],(A1.inverse_letter(e[2][0]),e[2][1]))
                for i,b in enumerate(start_letters):
                    bb=A0.inverse_letter(b)
                    if bb in end_letters:
                        local_start_letters=start_letters[:i]+start_letters[i+1:]
                        local_end_letters=[c for c in end_letters if c!=bb]
                        
                        holes.append([e,(b,0),local_start_letters,end_letters])
                        holes.append([ee,(b,0),end_letters,local_start_letters])
                        holes.append([e,(bb,0),start_letters,local_end_letters])
                        holes.append([ee,(bb,0),local_end_letters,start_letters])
                        if verbose:
                            print holes[-4:]

        # Adding holes corresponding to twice light squares not yet acknowledge by the permutation

        for sq in self.twice_light_squares():
            a=sq[4]
            b=sq[5]
            ap=A0.to_positive_letter(a)
            aa=A0.inverse_letter(a)
            bb=A1.inverse_letter(b)
            if (ap,0) not in permutation or permutation[(ap,0)]!=sq[5]:
                if verbose:
                    print "Twice light square not yet acknowledge by the permutation:",sq
                start_letters=[]
                end_letters=[c for c in A0 if c!=aa and c!=a]
                holes.append([[sq[1],sq[2],(b,1)],(aa,0),start_letters,end_letters+[a]])
                holes.append([[sq[1],sq[2],(b,1)],(a,0),start_letters+[aa],end_letters])
                holes.append([[sq[2],sq[1],(bb,1)],(aa,0),end_letters+[a],start_letters])
                holes.append([[sq[2],sq[1],(bb,1)],(a,0),end_letters,start_letters+[aa]])
                if verbose:
                    print holes[-4:]
                    
                

        i=0
        surgeries=[]
        symetric_surgeries=[]

        while i<len(holes):
            a=holes[i][0][2][0]
            ap=A1.to_positive_letter(a)
            if a==ap:
                orap=-1
            else:
                orap=1

            b=holes[i][1][0]
            bp=A0.to_positive_letter(b)

            bb=A0.inverse_letter(b)

            if (bb in holes[i][2]) ^ (b==bp):
                orbp=1
            else:
                orbp=-1

            if (ap,side) not in orientation or orientation[(ap,side)]==orap:                
                surgeries.append([((ap,side),orap),((bp,1-side),orbp)])
                if (((ap,side) not in permutation) or (bp==permutation[(ap,side)])) and\
                        (((bp,1-side) not in permutation) or (ap==permutation[(bp,1-side)])):
                    symetric_surgeries.append(i)
                i+=1
            else:
                holes.pop(i)

        
                

        if verbose:
            print "Symetric surgeries:",[surgeries[i] for i in symetric_surgeries]


        if force_surgery is not None:
            i=0
            while surgeries[i]!=force_surgery:
                i+=1
        elif len(symetric_surgeries)>0:
            i=symetric_surgeries[0]

        else:
            if verbose:
                print "No more symetric surgeries, specify one using option force_surgery:"
                for i,surgery in enumerate(surgeries):
                    print i, ":",surgery
            raise NoSymmetricSurgeryException(surgeries)


        hole=holes[i]

        if verbose:
            print "Using symetric surgery:", surgeries[i]

        moves=C.rips_machine_moves(holes=[hole])

        psi=FreeGroupAutomorphism(moves[0])
        if verbose:
            print "and automorphism:",psi


        phi=phi*psi
        phi=phi.simple_outer_representative()

        if verbose:
            print "Current automorphism:",phi


        orientation[surgeries[i][0][0]]=surgeries[i][0][1]
        orientation[surgeries[i][1][0]]=surgeries[i][1][1]
        permutation[surgeries[i][0][0]]=surgeries[i][1][0][0]
        permutation[surgeries[i][1][0]]=surgeries[i][0][0][0]

        C=ConvexCoreWithRipsMachine(phi)

        return surgeries[i],C,orientation,permutation


    def unicorn_surgery_path(self,side=1,cyclic_order_0=None,cyclic_order_1=None,reverse=False,verbose=False,save=False):

        C=self

        path="/home/coulbois/recherche/sage-tex/"
        count=0
        g=C.plot_ideal_curve_diagram(cyclic_order_0=cyclic_order_0,cyclic_order_1=cyclic_order_1,verbose=verbose and verbose>2 and verbose-2)
        title="0:"   #%s"%self._f01
        if save:
            filename=path+"unicorn+%s.png"%count
            g.save(filename=filename,title=title)
        g.show(title=title)
        if reverse:
            pphi0=C._f10.simple_outer_representative()
            g=ConvexCore(pphi0).plot_ideal_curve_diagram(cyclic_order_0=cyclic_order_0,cyclic_order_1=cyclic_order_1,verbose=verbose and verbose>2 and verbose-2)
            title="-0:"   #%s"%self._f01
            if save:
                filename=path+"unicorn-%s.png"%count
                g.save(filename=filename,title=title)
            g.show(title=title)
        
        orientation=dict()
        permutation=dict()

        while C.volume()>0 or len(C.isolated_edges())>0:
            try: 
                surgery,C,orientation,permutation=C.unicorn_surgery_step(side=side,orientation=orientation,permutation=permutation,verbose=verbose and verbose>1 and verbose-1)
                count+=1
                if verbose:
                    print count,": Symmetric surgery:",surgery


                g=C.plot_ideal_curve_diagram(cyclic_order_0=cyclic_order_0,cyclic_order_1=cyclic_order_1,verbose=verbose and verbose>2 and verbose-2)
                title="%s:%s"%(count,surgery)
                if save:
                    filename=path+"unicorn+%s.png"%count
                    g.save(filename=filename,title=title)
                g.show(title=title)
                if reverse:
                    phi=C._f01
                    CC=ConvexCore((pphi0*phi).simple_outer_representative())
                    g=CC.plot_ideal_curve_diagram(cyclic_order_0=cyclic_order_0,cyclic_order_1=cyclic_order_1,verbose=verbose and verbose>2 and verbose-2)
                    title="-%s:"%count   #%s"%self._f01
                    if save:
                        filename=path+"unicorn-%s.png"%count
                        g.save(filename=filename,title=title)
                    g.show(title=title)

            except NoSymmetricSurgeryException as surgeries:
                if verbose:
                    print "No single symmetric surgery, looking for a cycle"
                    print "Surgeries:",surgeries.args[0]
                    print "Permutation:",permutation
                surgeries=surgeries.args[0]
                A1=C.tree(side=side).alphabet()
                surgery_permutation=dict((surgery[0][0],surgery[1][0]) for surgery in surgeries)
                next=dict()
                cycles_starts=[]
                for b,side in surgery_permutation.keys():
                    current_next=dict()
                    b0=b
                    while b not in current_next:
                        a= surgery_permutation[(b,side)]
                        if a in permutation:
                            current_next[b]=permutation[a]
                            b=current_next[b]
                        elif (b0,side) not in permutation:
                            b=b0
                        else:
                            break
                    else:
                        cycles_starts.append(b)
                
                max_cycles_len=A1.cardinality()+1
                shortest_cycle=None

                for b0 in cycles_starts:
                    cycle=[b0]
                    b=permutation[surgery_permutation[(b0,side)]]
                    while b!=b0:
                        cycle.append(b)
                        a=surgery_permutation[(b,side)]
                        if a in permutation:
                            b=permutation[a]
                        else:
                            b=b0
                    if len(cycle)<max_cycles_len:
                        shortest_cycle=cycle
                        max_cycles_len=len(cycle)

                if verbose:
                    print "Symmetric cycle of surgeries:",shortest_cycle
                    for b in shortest_cycle:
                        for surgery in surgeries:
                            if surgery[0][0][0]==b and surgery_permutation[(b,side)]==surgery[1][0]:
                                print surgery
                                break

                for b  in shortest_cycle:
                    for surgery in surgeries:
                        if surgery[0][0][0]==b and surgery_permutation[(b,side)]==surgery[1][0]:
                            break
                      
                    surgery,C,orientation,permutation=C.unicorn_surgery_step(side=side,force_surgery=surgery,orientation=orientation,permutation=permutation,verbose=verbose and verbose>1 and verbose-1)
                    if verbose:
                        print "Surgery:",surgery

                    count+=1
                    g=C.plot_ideal_curve_diagram(cyclic_order_0=cyclic_order_0,cyclic_order_1=cyclic_order_1,verbose=verbose and verbose>2 and verbose-2)
                    title="%s (intermediate):%s"%(count,surgery)
                    if save:
                        filename=path+"unicorn+%s.png"%count
                        g.save(filename=filename,title=title)
                    g.show(title=title)
                    if reverse:
                        phi=C._f01
                        CC=ConvexCore((pphi0*phi).simple_outer_representative())
                        g=CC.plot_ideal_curve_diagram(cyclic_order_0=cyclic_order_0,cyclic_order_1=cyclic_order_1,verbose=verbose and verbose>2 and verbose-2)
                        title="-%s:"%count   #%s"%self._f01
                        if save:
                            filename=path+"unicorn-%s.png"%count
                            g.save(filename=filename,title=title)
                        g.show(title=title)

                    
                    permutation[surgery[0][0]]=surgery[1][0][0]
                    permutation[surgery[1][0]]=surgery[0][0][0]
                    
                


class NoSymmetricSurgeryException(Exception):
    pass
    
