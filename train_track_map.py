#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from topological_representative import TopologicalRepresentative
from sage.combinat.words.morphism import WordMorphism
from sage.combinat.words.word import Word
from sage.combinat.words.words import FiniteWords
from sage.graphs.graph import Graph
from sage.rings.qqbar import AA
from sage.matrix.constructor import matrix

class TrainTrackMap(TopologicalRepresentative):
    """
    A train-track map is a map from a (possibly marked, possibly
    metric) graph to itself which is train track: vertices are mapped
    to vertices, edges are mapped to non-trivial reduced edge paths
    and no cancellation occures in the iterated images of edges.

    Note that a train-track map can be also a relative train-track: it
    may have a stratified structure.

    Train-tracks are intended to be constructed by promoting
    topological representative that satisfies the train-track
    definition.

    EXAMPLES::

    sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")
    sage: f=phi.rose_representative()
    sage: tt=TrainTrack(f)
    sage: print tt
    
    sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a")
    sage: phi=phi.inverse()
    sage: tt=phi.train_track()
    sage: print tt

    AUTHORS:

    - Thierry Coulbois (2014-07-22): beta.1 version
    """


    def __init__(self,*args):
        """
        The following forms are accepted:
        
        - ``TrainTrackMap(f)`` where ``f`` is a
        TopologicalRepresentative which is train-track (no check is
        done)

        - ``TrainTrackMap(graph,edge_map,vertex_map=None)`` where
          ``graph`` is a ``GraphWithInverses`` and ``edge_map`` is
          anything accepted by ``WordMorphism(edge_map)`` with domain
          alphabet an ``AlphabetWithInverses`` (only one of each pair
          (a,inverse_letter(a)) need to have an image by
          ``edge_map``).
        """
        
        TopologicalRepresentative.__init__(self,*args)
 
    def __str__(self):
        """
        String representation of ``self``.
        """
        result="Train-track map:\n"
        result+=self._domain.__str__()+"\n"
        result+="Edge map: "
        for a in self._domain._alphabet.positive_letters():
            result+=a+"->"
            for b in self.image(a):
                result+=b
            result+=", "
        result=result[:-2]
        if self._strata:
            if len(self._strata)==1:
                result+="\nIrreducible representative"
            else:
                result+="\nStrata: "+self._strata.__str__()

        return result

    def is_train_track(self,verbose=False):
        """
        Returns ``True``.
        """
        return True
    
    @staticmethod
    def from_edge_map(edge_map,alphabet=None,path=None):
        """
        Builds a train-track map from an edge map.

        The graph is computed to be the biggest possible graph for
        which the edge_map is continuous. Additionnal information can
        be given in ``path``, the graph must admit ``path`` as an
        edge-path.

        The marking is chosen by picking a maximal forest in the graph
        and identifying the other edges, with generators of a free
        group.

        INPUT:

        - ``edge_map`` anything which is accepted by
        ``WordMorphism(edge_map)``, the letters must be from an
        ``AlphabetWithInverses``. Its is only required that images of
        positive letters are defined.

        - ``path`` (default None) an admissible edge-path in the base
          graph of ``self``.

        EXAMPLES::

        sage: print TrainTrackMap.from_edge_map("a->ec,b->Ea,c->b,e->C")
        Train-track map:
        Graph with inverses: a: 0->0, b: 1->0, c: 1->0, e: 0->1
        Edge map: a->ec, b->Ea, c->b, e->C
        """

        return TrainTrackMap(TopologicalRepresentative.from_edge_map(edge_map,alphabet,path))

    def is_expanding(self):
        """
        ``True`` if ``self`` is an expanding train-track map.

        A train-track is expanding of for each edge e, the iterated
        images of e get infinitely long: lim_{n\to\infty}
        f^n(e)=+\infty. Equivalently for any edge e, there exists n
        such that the length of f^n(e) is larger or equal to 2.
        """

        done=True
        edges=self.domain().alphabet().positive_letters()[:]
        i=0
        while i<len(edges):
            e=edges[i]
            if len(self.image(e))>1: #e is expanded
                done=False
                edges.pop(i)
            else:
                i+=1
                
        #only not expanded edges are left in edges
        while not done:
            done=True
            i=0
            while i<len(edges):
                e=edges[i]
                if self.image(e)[0] not in edges: #e is eventually expanded
                    done=False
                    edges.pop(i)
                else:
                    i+=1
        return len(edges)==0   # edges contains all the never expanded edges

    def is_perron_frobenius(self):
        """
        ``True`` if (the matrix of) ``self`` satisfies the hypothesis of
        Perron-Frobenius theorem.

        (The matrix of) ``self`` is Perron-Frobenius if it has a power
        with strictly positive entries.

        Note that if ``self`` is not Perron-Frobenius then it has a
        disconnected local Whitehead graph (the converse is false).

        SEE ALSO::

        TrainTrackMap.has_connected_local_whitehead_graphs()
        """
        if len(self.stratify())>1:
            return False
        #Now, we know that self is irreducible
        
        A=self.domain().alphabet()
        image=dict([]) #set of edges that appears in the image of an edge
        
        for a in A.positive_letters():
            image[a]=set([A.to_positive_letter(b) for b in self.image(a)])
        stable_image=image.copy() 

        a=A[0]
        while a not in stable_image[a]: #this loop will terminate because self is irreducible
            for b in A.positive_letters():
                stable_image[b]=set([d for c in stable_image[b] for d in image[c]])

        image=stable_image #we now work with the power of self for which a occurs in self^n(a)

        done=False
        while not done:
            done=True
            next=dict()
            for b in A.positive_letters():
                next[b]=set([d for c in stable_image[b] for d in image[c]])
                if len(next[b])>len(stable_image[b]):
                    done=False
            stable_image=next

        image=stable_image #now the image of self^n(a) is maximal

        if len(image[a])<len(A):
            return False

        #we now look for letters from which we can reach a

        good_letters=set([b for b in A.positive_letters() if a in image[b]])
        bad_letters=set([b for b in A.positive_letters() if b not in good_letters])

        done=False
        while not done:
            done=True
            for b in bad_letters:
                if len(image[b].intersection(good_letters))>0:
                    good_letters.add(b)
                    done=False
            bad_letters=set([b for b in A.positive_letters() if b not in good_letters])

        return len(bad_letters)==0
        


    def gates(self,v):
        """
        List of gates at vertex ``v``.

        A gate is a list of edges starting at vertex ``v`` such each
        to of them form an illegal turn. That is to say after
        iteration of ``self`` the two edges have a common prefix.

        OUTPUT:
        
        list of list of edges out of the vertex ``v``.

        AUTHOR: 

        Brian Mann
        """

        gates=[]

        illegal_turns=self.illegal_turns(v)

        for e in self.domain().alphabet():
            if self.domain().initial_vertex(e) == v:
                for g in gates:
                    if (g[0],e) in illegal_turns:
                        g.append(e)
                        break
                else:
                    gates.append([e])

        return gates

    def number_of_gates(self,v=0):
        """
        Number of gates at v.

        SEE ALSO::

        TrainTrackMap.gates(self)
        """
        return len(self.gates(v))

    def local_whitehead_graph(self,v):
        """
        The local whitehead graph at a vertex ``v``. 

        Vertices are directions at v, and two directions are joined by
        an edge if some iterate of an edge by ``self` crosses that turn.

        AUTHOR: 

        Brian Mann
        """
            
        edges=[(e,f) for (e,f) in self.edge_turns() if self.domain().initial_vertex(e)==v]
        
        return Graph(edges)

    def stable_local_whitehead_graph(self,v):
        """
        The stable local Whitehead graph at a vertex ``v``.
        
        Vertices are stable directions at ``v`` (stable directions are
        in one-to-one correspondence with gates). Two directions are
        joined by an edge if some iterate of an edge`by
        ``self``crosses that turn.

        The stable local Whitehead graph is a subgraph of the local
        Whitehead graph.

        Note that if ``v`` is not a periodic vertex then its stable
        local Whitehead graph is empty.

        """
        
        lwg=self.local_whitehead_graph(v)
        
        directions=lwg.vertices()
        images=directions

        #Looking for a period for the vertex v
        
        reached_vertices=set([v])
        w=v
        done=False
        while not done:
            w=self(w)
            images=[self.image(e)[0] for e in images]
            if w in reached_vertices:
                done=True
            else:
                reached_vertices.add(w)

        if w!=v:
            return Graph()

        done=False
        while not done:
            done=True
            for i,e in enumerate(directions):
                if e not in images:
                    directions.pop(i)
                    images.pop(i)
                    done=False
        
        return lwg.subgraph(vertices=directions)
  
    def indivisible_nielsen_paths(self,verbose=False):
        """
        The list of indivisible Nielsen paths of ``self``.

        WARNING:

        ``self`` is assumed to be an expanding train-track map.

        OUPUT:

        A list of INPs. Each INP is returned as a pair of word-paths, the fixed
        points lie inside the extremal edges of the words.

        SEE ALSO::

        TopologicalRepresentative.relative_indivisible_nielsen_paths()
        TrainTrackMap.periodic_nielsen_paths()
        """

        G=self._domain
        A=G._alphabet

        result=[]
        image=[]
        next=[]

        extension=dict((a,[]) for a in A)

        edge_turns=self.edge_turns()
        for t in edge_turns:
            extension[A.inverse_letter(t[0])].append(t[1])
            extension[A.inverse_letter(t[1])].append(t[0])

        fold_turns=self.fold_turns()
        for t in fold_turns:
            result.append((Word(),Word()))
            image.append((Word(),Word())) #tigthen image of result
            next.append((t[0],t[1])) #letters to add to result

        u=[None,None]
        uu=[None,None]

        i=0
        while i<len(result):
            t=result.pop(i)
            tt=image.pop(0)
            ext=next.pop(0)

            for j in xrange(2):
                if ext[j]!=None:
                    u[j]=t[j]*Word([ext[j]])
                    uu[j]=tt[j]*self.image(ext[j])
                else:
                    u[j]=t[j]
                    uu[j]=tt[j]

            t=(u[0],u[1])
            p=G.common_prefix_length(uu[0],uu[1])
            tt=(uu[0][p:],uu[1][p:])

            if verbose: print t[0],t[1]," image: ", tt[0],",",tt[1]

            if len(tt[0])==0:
                for a in extension[t[0][-1]]:
                    result.insert(i,t)
                    image.insert(0,tt)
                    next.insert(0,(a,None))

            elif len(tt[1])==0:
                for a in extension[t[1][-1]]:
                    result.insert(i,t)
                    image.insert(0,tt)
                    next.insert(0,(None,a))


            elif (G.is_prefix(t[0],tt[0]) and G.is_prefix(t[1],tt[1])):
                    result.insert(i,t)
                    if verbose: print "inp"
                    i+=1


            elif G.is_prefix(tt[0],t[0]) and len(tt[0])<len(t[0]) and (G.is_prefix(t[1],tt[1]) or G.is_prefix(tt[1],t[1])):
                for a in extension[t[0][-1]]:
                    result.insert(i,t)
                    image.insert(0,tt)
                    next.insert(0,(a,None))

            elif G.is_prefix(tt[1],t[1]) and G.is_prefix(t[0],tt[0]):
                for a in extension[t[1][-1]]:
                    result.insert(i,t)
                    image.insert(0,tt)
                    next.insert(0,(None,a))

        return result

    def periodic_nielsen_paths(self,end_points=False,verbose=False):
        """
        List of periodic Nielsen paths.


        WARNING:

        ``self`` is assumed to be an expanding train-track map.

        OUTPUT:

        A list of tuples ``(word1,word2,period)``. The fixed points lie in the last edge
        of the two words.

        SEE ALSO::
        
        TrainTrackMap.indivisible_nielsen_paths()
        """

        G=self.domain()
        A=G.alphabet()
        N=len(A)
        

        possible_np=[] #long illegal turns that have not yet been ruled out
        images=[] #images of the possible inp
        next=[]  # edges to add to the corresponding possible_np

        extension=dict((a,[]) for a in A) # Possible extensions a a legal path ending by a

        edge_turns=self.edge_turns()
        for t in edge_turns:
            extension[A.inverse_letter(t[0])].append(Word([t[1]]))
            extension[A.inverse_letter(t[1])].append(Word([t[0]]))

        for t in self.illegal_turns():
            possible_np.append((Word([t[0]]),Word([t[1]])))
            uu=self.image(t[0])
            vv=self.image(t[1])
            p=G.common_prefix_length(uu,vv)            
            images.append((uu[p:],vv[p:])) #tigthen image of possible_np
            next.append((Word([]),Word([]))) #letters to add to possible_np


                    
        i=0
        done=False
        while (not done or i>0) and len(possible_np)>0:
            if i==0:
                done=True
            t=possible_np[i] #will need to compare t with its image
            n=next.pop(i)
            image=images.pop(i)

            if len(n[0])>0 or len(n[1])>0:
                done=False
            u=t[0]*n[0]
            v=t[1]*n[1]
            uu=image[0]*self(n[0])
            vv=image[1]*self(n[1])
            p=G.common_prefix_length(uu,vv)
            uu=uu[p:]
            vv=vv[p:]

            if verbose:
                print "possible Nielsen path:",u,v,
                print " reduced image:",uu,",",vv,

            if len(uu)==0:
                if verbose: print "extend"
                done=False
                possible_np.pop(i)
                for a in extension[u[-1]]:
                    possible_np.insert(i,(u,v))
                    images.insert(i,(uu,vv))
                    next.insert(i,(a,Word([])))
            elif len(vv)==0:
                if verbose: print "extend"
                done=False
                possible_np.pop(i)
                for a in extension[v[-1]]:
                    possible_np.insert(i,(u,v))
                    images.insert(i,(uu,vv))
                    next.insert(i,(Word([]),a))
            else:
                compatible=False
                for tt in possible_np:
                    for j in xrange(2):
                        p=G.common_prefix_length(tt[j],uu)
                        q=G.common_prefix_length(tt[1-j],vv)
                        if (len(uu)==p or len(tt[j])==p) and (len(vv)==q or len(tt[1-j])==q): # (uu,vv) is compatible with (tt[j],tt[1-j])
                            compatible=True
                            possible_np.pop(i) # we will add it back immediatly
                            if verbose:
                                print "compatible with:",tt[j],tt[1-j]
                            if p<len(tt[j]): #uu is a strict prefix of tt[j]: we have to extend u
                                done=False
                                for a in extension[u[-1]]:
                                    possible_np.insert(i,(u,v))
                                    images.insert(i,(uu,vv))
                                    next.insert(i,(a,Word([])))
                                break
                            elif q<len(tt[1-j]):  #vv is a strict prefix of tt[1-j]: we have to extend v
                                done=False
                                for a in extension[v[-1]]:
                                    possible_np.insert(i,(u,v))
                                    images.insert(i,(uu,vv))
                                    next.insert(i,(Word([]),a))    
                                break
                            else:  #we do not know yet what to extend
                                possible_np.insert(i,(u,v))
                                images.insert(i,(uu,vv))
                                next.insert(i,(Word([]),Word([])))
                                i=i+1
                                break
                    if compatible:
                        break
                else:
                    if verbose:
                        print "not compatible with possible Nielsen paths"
                    possible_np.pop(i)
                    done=False
            if i>=len(possible_np):
                i=0

        if verbose:
            print "List of possible Nielsen paths:"
            print possible_np

        # Now we look for periodic points among possible_np

        # We build a map on indices

        if verbose:
            print "Building the list of stable possible Nielsen paths (given by their index):",

        found=False
        m=dict()
        for i,t in enumerate(images):
            found=False
            for j,tt in enumerate(possible_np):
                for k in xrange(2):
                    p=G.common_prefix_length(t[0],tt[k])
                    q=G.common_prefix_length(t[1],tt[1-k])
                    if p==len(tt[k]) and q==len(tt[1-k]): # tt is a subturn of t
                        m[i]=(j,1-2*k)
                        found=True
                        break
                if found: break
        
        stable=m.keys()
        old_stable=len(stable)+1
        while len(stable)<old_stable:
            stable, old_stable= set(m[i][0] for i in stable), len(stable)
        
        if verbose:
            print stable

        pnps=[]

        while 0<len(stable):
            iter=1
            i=stable.pop()
            j=i
            k=1
            while m[j][0]!=i:
                j,k=(m[j][0],m[j][1]*k)
                iter+=1
            if k*m[j][1]==-1:
                iter=2*iter
            pnps.append((possible_np[i],iter))
            j=i
            while m[j][0]!=i:
                j=m[j][0]
                pnps.append((possible_np[j],iter))
                stable.remove(j)
          
        if end_points:
            #the end of an inp is either a vertex of self or a point
            #inside an edge which is denoted by (e,period,portion) or
            #(e,period,left,right)
        
            if verbose:
                print "Looking for endpoints"

            maxl=1
            for ((u,v),period) in pnps:
                maxl=max([maxl,len(u),len(v)])

            M=self.matrix()

            for i,((u,v),period) in enumerate(pnps):
                if verbose:
                    print "Periodic Nielsen path:",((u,v),period),
                if period==1:
                    uu=self(u)
                    vv=self(v)
                    p=G.common_prefix_length(uu,vv)
                    right1=len(uu)-len(u)-p
                    right2=len(vv)-len(v)-p
                    left1=len(self(u[-1]))-right1-1
                    left2=len(self(v[-1]))-right2-1
                else:
                    uu=u
                    vv=v
                    prefix_ab=matrix(len(A),1) # abelianized form of the prefix
                    for j in xrange(period):
                        uu=self(uu)
                        vv=self(vv)
                        p=G.common_prefix_length(uu,vv)
                        new_prefix_ab=matrix(N,1)
                        for a in uu[:p]:
                            new_prefix_ab[A.rank(a)%N,0]+=1
                        #new_prefix_ab=uu[:p].abelian_vector()
                        #new_prefix_ab=matrix(len(A),1,[new_prefix_ab[k]+new_prefix_ab[k+len(A)] for k in xrange(len(A))])
                        prefix_ab=M*prefix_ab+new_prefix_ab
                        uu=uu[p:p+maxl]
                        vv=vv[p:p+maxl]

                    prefix_len=sum(prefix_ab.column(0))

                    Mperiod=M**period

                    u_ab=matrix(N,1)
                    for a in u:
                        u_ab[A.rank(a)%N,0]+=1
                    #u_ab=u.abelian_vector()
                    #u_ab=matrix(len(A),1,[u_ab[k]+u_ab[k+len(A)] for k in xrange(len(A))])
                    uu_ab=Mperiod*u_ab
                    right1=sum(uu_ab.column(0))-prefix_len-len(u)

                    v_ab=matrix(N,1)
                    for a in v:
                        v_ab[A.rank(a)%N,0]+=1
                    #v_ab=v.abelian_vector()
                    #v_ab=matrix(len(A),1,[v_ab[k]+v_ab[k+len(A)] for k in xrange(len(A))])
                    vv_ab=Mperiod*v_ab
                    right2=sum(vv_ab.column(0))-prefix_len-len(v)

                    left1=sum(Mperiod.column(A.rank(A.to_positive_letter(u[-1]))))-right1-1
                    left2=sum(Mperiod.column(A.rank(A.to_positive_letter(v[-1]))))-right2-1

                v1=(u[-1],period,left1,right1) 
                v2=(v[-1],period,left2,right2)

                if v1[3]!=0: # vertex in the middle of an edge
                    v1=self.periodic_point_normal_form(v1,keep_orientation=True,verbose=(verbose and verbose>1 and verbose-1))
                    vv1=(A.inverse_letter(v1[0]),v1[1],v1[3],v1[2])
                else:
                    vv1=(A.inverse_letter(v1[0]),)

                if v2[3]!=0: # vertex in the middle of an edge
                    v2=self.periodic_point_normal_form(v2,keep_orientation=True,verbose=(verbose and verbose>1 and verbose-1))
                    vv2=(A.inverse_letter(v2[0]),v2[1],v2[3],v2[2]) 
                else:
                    vv2=(A.inverse_letter(v2[0]),)

                # build the germ classes of germs ending pnps

                if verbose:
                    print "Ending germs:",vv1,"and",vv2

                pnps[i]=((u,v),period,(vv1,vv2))

        return pnps
                        

    def fold_inp(self,inp,verbose=False):
        """
        Recursively folds a  non-essential inp until a partial fold
        occurs and the inp is removed.

        INPUT:

        ``inp``a couple ``(word1,word2)``, the invariant points being
        inside the last letters of the two words.

        OUTPUT:

        A ``WordMorphism`` that maps old edges to paths in the new
        graph.

        WARNING:

        - Calling this method with an essential inp will cause an
        infinite loop.

        - Beware this has no effect on the possible strata of self.
        """

        result_morph=False

        done=False
        while not done:
            done=True
            if verbose:
                print "Fold inp: ",inp[0],inp[1]
            image=(self.image(inp[0][0]),self.image(inp[1][0]))
            prefix_length=self._domain.common_prefix_length(image[0],image[1])
            if len(image[0])==prefix_length or len(image[1])==prefix_length:
                done=False
                folding_morph=self.fold([inp[0][0],inp[1][0]],image[0][0:prefix_length],verbose=verbose)
                if result_morph:
                    result_morph=folding_morph*result_morph
                else:
                    result_morph=folding_morph
                inp=[folding_morph(inp[0]),folding_morph(inp[1])]
                prefix_length=self._domain.common_prefix_length(inp[0],inp[1])
                inp=[inp[0][prefix_length:],inp[1][prefix_length:]]
            else:
                if verbose: print "Partial fold"
                full_edges=[]
                partial_edges=[]
                full_done=False
                for i in xrange(2):
                    if not full_done and len(self.image(inp[i][0]))==prefix_length+1: #TODO there is a problem if both edges satisfies this
                        full_edges.append(inp[i][0])                             # Added the done condition. Fixed ? TODO: check
                        full_done=True
                    else:
                        partial_edges.append(inp[i][0])

                if verbose: print "Fold: full edges: ",full_edges," partial edges: ",partial_edges

                folding_map=self._domain.fold(full_edges,partial_edges)
                folding_morph=WordMorphism(folding_map)

                if result_morph:
                    result_morph=folding_morph*result_morph
                else:
                    result_morph=folding_morph


                edge_map=dict((folding_map[a][0], folding_morph(self.image(a))) for a in self._edge_map.domain().alphabet() if len(folding_map[a])==1)

                if len(partial_edges)==2 and len(folding_map[partial_edges[0]])==3:
                    a=partial_edges[0]
                    c=folding_map[a][1]

                    edge_map[c]=folding_morph(self.image(a)[prefix_length:-prefix_length])[1:-1]

                else:
                    for a in partial_edges:
                        b=folding_map[a][1]
                        edge_map[b]=folding_morph(self.image(a)[prefix_length:])[1:]

                c=folding_map[inp[0][0]][0]
                edge_map[c]=folding_morph(self.image(inp[0][0])[:prefix_length])*Word([c])


                self.set_edge_map(edge_map)

                if verbose: print "\n",self

        return result_morph

        
    def stabilize(self,verbose=False):
        """
        Given an irreducible train-track representative, computes a
        stable train-track representative by folding non-essential
        inps or finds a reduction.
        """
        A=self._domain.alphabet()
        result_morph=False

        done=False
        while not done:
            done=True
            inps=self.indivisible_nielsen_paths(verbose=(verbose and verbose-1))
            if verbose:
                print "INPs: ",inps
            if len(inps)==0:
                return WordMorphism(dict((a,a) for a in self._domain._alphabet))

            M=self.matrix()
            vectors=M.eigenvectors_left()
            pf=0
            for (e,v,n) in vectors:
                if e in AA and e>pf:
                    pfv=v[0]
                    pf=e
            critic=0
            for i in xrange(len(A)):
                critic+=pfv[i]
            critic=critic*(pf-1)
            for inp in inps:
                prefix=self(inp[0])[:self._domain.common_prefix_length(self(inp[0]),self(inp[1]))]
                prefix_length=0
                for a in prefix:
                    prefix_length+=pfv[A.rank(A.to_positive_letter(a))]
                if prefix_length!=critic:
                    done=False
                    if verbose:
                        print "Non essential INP: ",inp
                    self._strata=False
                    folding_morph=self.fold_inp(inp,verbose)
                    if result_morph:
                        result_morph=folding_morph*result_morph
                    else:
                        result_morph=folding_morph
                    break
            else:
                for turn in self._domain.turns():
                    tt=self.image_turn(turn)
                    if tt[0]==tt[1] and any((turn[0]!=inp[0][0] or turn[1]!=inp[1][0]) for inp in inps):
                        done=False
                        if verbose: print "Fold illegal turn: ",turn
                        prefix=self.image(turn[0])[0:self._domain.common_prefix_length(self.image(turn[0]),self.image(turn[1]))]
                        self._strata=False
                        folding_morph=self.fold(turn,prefix,verbose)
                        if result_morph:
                            result_morph=folding_morph*result_morph
                        else:
                            result_morph=folding_morph
                        break
                else:
                    for turn in self._domain.turns():
                        tt=self.image_turn(turn)
                        if any((tt[0]==inp[0][0] and tt[1]==inp[1][0]) for inp in inps):
                            done=False
                            if verbose: print "Fold illegal turn :",tt
                            prefix=self.image(tt[0])[0:self._domain.common_prefix_length(self.image(tt[0]),self.image(tt[1]))]
                            self._strata=False
                            folding_morph=self.fold(tt,prefix,verbose)
                            if result_morph:
                                result_morph=folding_morph*result_morph
                            else:
                                result_morph=folding_morph
                            break

            if not done:
                reduce_morph=self.reduce(verbose)
                result_morph=reduce_morph*result_morph




            if verbose:
                if len(self._strata)>1:
                    print "Strata: ",self._strata
                else:
                    print "Irreducible representative"


            if len(self._strata)>1:
                done=True

        return result_morph

    def has_connected_local_whitehead_graphs(self,verbose=False):
        """
        ``True`` if all local Whitehead graphs are connected.

        EXAMPLE::

        sage: phi=FreeGroupAutomorphism("a->bca,b->bcacacb,c->cac")
        sage: f=TrainTrackMap(phi.rose_representative())
        sage: f.has_connected_local_whitehead_graphs()


        SEE ALSO::
        
        TrainTrackMap.local_whitehead_graph()
        TrainTrackMap.whitehead_connected_components()
        """
        
        return len(self.whitehead_connected_components(verbose))==len(self.domain().vertices())
        

    def periodic_nielsen_loops(self,pnps=None,verbose=False):
        """
        List of loops made of periodic Nielsen paths.

        Such a loop is a periodic element of ``self``.

        INPUT:

        ``pnps``: the list of periodic Nielsen paths. Each given as
        ``((u1,u2),period,(vv1,vv2))``.

        OUTPUT:

        A list of ``(loop,vertex,period)`` where ``loop`` is a
        periodic Nielsen loop, ``vertex`` is a periodic point which is
        a based point of the loop.

        WARNING:
        
        If ``pnps`` are not given, computes the periodic Nielsen paths
        using ``TrainTrackMap.periodic_nielsen_paths(self)``.  Thus
        assumes that ``self`` is an expanding train-track.
        """
        from sage.rings.arith import lcm

        G=self.domain()
        A=G.alphabet()

        if verbose:
            print "Looking for periodic Nielsen loops"

        if pnps==None:
            pnps=self.periodic_nielsen_paths(end_points=True,verbose=verbose and verbose>1 and verbose-1)

        if verbose:
            print "Periodic Nielsen paths:",pnps

        components_tree=dict([]) # maps a vertex v to (vv,w) where w is Nielsen path from v to vv
        loops=[]

        for i,((u1,u2),period,(v1,v2)) in enumerate(pnps):

            if len(v1)==4: # vertex in the middle of an edge of the form v1=(a,period,left,right)
                if not A.is_positive_letter(v1[0]):
                    v1=(A.inverse_letter(v1[0]),v1[1],v1[3],v1[2])
            else: # vertex at the origin of the germ: v1=(a,)
                v1=(G.initial_vertex(v1[0]),)

            if len(v2)==4: # vertex in the middle of an edge of the form v2=(a,period,left,right)
                if not A.is_positive_letter(v2[0]):
                    v2=(A.inverse_letter(v2[0]),v2[1],v2[3],v2[2])
            else: # vertex at the origin of the germ: vv2=(a,)
                v2=(G.initial_vertex(v2[0]),)

            if verbose:
                print "periodic Nielsen path (",u1,",",u2,") linking vertices",v1,"and",v2

            if v1==v2: # this pNp is a loop
                if verbose: print "Loop at vertex",v1
                if len(v1)==4:
                    loops.append((G.reduce_path(G.reverse_path(u1)*u2[:-1]),v1,period))
                else:
                    loops.append((G.reverse_path(u1)*u2,v1,period))

            elif v1 in components_tree and v2 in components_tree:
                vv1,w1,period1=components_tree[v1]
                vv2,w2,period2=components_tree[v2]
                period=lcm([period,period1,period2])
                if len(v1)==4 and len(w1)>0 and w1[-1]!=u1[-1]: #The Nielsen paths w1 and pnp form a reduce path
                    link1=w1*G.reverse_path(u1[:-1]) #Nielsen path from vv1 to the tip of the pnp
                else:
                    link1=w1*G.reverse_path(u1)              
                if len(u2)==4 or (len(w2)>0 and w2[-1]==u2[-1]):
                    link2=u2*G.reverse_path(w2)  #Nielsen path from the tip of the pnp to vv2
                else:
                    link2=u2[:-1]*G.reverse_path(w2)
                link=G.reduce_path(link1*link2)  #Nielsen path from vv1 to vv2
                if vv1==vv2:
                    if len(link)>0:
                        if len(vv1)==4 and len(link)>0 and link[0]==link[-1]:
                            link=link[:-1]
                    if len(link)>0:
                        if verbose:
                            print "loop at vertex",vv1,":",link
                        loops.append((link,vv1,period))
                    elif verbose:
                        print "contractable loop at vertex",vv1
                else:  #we fusion the two components
                    for (v,(vv,w,p)) in components_tree.iteritems():
                        if vv==vv2:
                            if len(vv2)==4 and len(link)>0 and len(w)>0 and w[0]==link[-1]:
                                components_tree[v]=(vv1,G.reduce_path(link[:-1]*w),lcm(p,period))
                            else:
                                components_tree[v]=(vv1,G.reduce_path(link*w),lcm(p,period))

            elif v1 in components_tree:
                vv1,w1,p1=components_tree[v1]
                if len(v1)==4 and len(w1)>0 and w1[-1]!=u1[-1]:
                    components_tree[v2]=(vv1,G.reduce_path(w1[:-1]*G.reverse_path(u1)*u2),lcm(p1,period))
                else:
                    components_tree[v2]=(vv1,G.reduce_path(w1*G.reverse_path(u1)*u2),lcm(p1,period))

            elif v2 in components_tree:
                vv2,w2,p2=components_tree[v2]
                if len(v2)==4 and len(w2)>0 and w2[-1]!=u2[-1]: 
                    components_tree[v1]=(vv2,G.reduce_path(w2[:-1]*G.reverse_path(u2)*u1),lcm(p2,period))
                else:
                    components_tree[v1]=(vv2,G.reduce_path(w2*G.reverse_path(u2)*u1),lcm(p2,period))
            else:
                components_tree[v1]=(v1,Word([]),1)
                components_tree[v2]=(v1,G.reverse_path(u1)*u2,period)

        #We order loops to remove multiple occurences of the same loop

        if verbose: print "Looking for multiple loops: Ordering the loops..."

        for n,loop in enumerate(loops):
            i=0
            j=1
            l=len(loop[0])
            while j<l:
                k=0
                smaller=False
                while k<l:
                    ki=i+k
                    kj=j+k
                    if ki>=l:
                        ki=ki-l
                    if kj>=l:
                        kj=kj-l
                    a=loop[0][ki]
                    b=loop[0][kj]
                    if A.less_letter(b,a):
                        if b!=a:
                            smaller=True
                            break
                    else:
                        break
                    k+=1
                if smaller: i=j
                j=j+1
            if verbose:
                print "Smallests cyclic conjugate of",loop,":",
            loops[n]=(loop[0][i:]+loop[0][:i],loop[1],loop[2])
            if verbose:
                print loops[n]

        i=0
        j=1
        while j<len(loops):
            if loops[i][0]==loops[j][0]:
                if verbose:
                    print loops[i],"occures twice"
                loops.pop(j)
            else:
                j+=1
            if j==len(loops):
                i+=1
                j=i+1

        return loops
                    
    def ideal_whitehead_graph(self,pnps=None,verbose=False):
        """
        The ideal Whitehead graph of ``self``.

        This is defined in [Handel-Mosher], see also [Pfaff] and is an
        invariant of the conjugacy class of the outer automorphism
        represented by ``self``.

        As an artefact we add 2 x rank(Stab) vertices to connected
        components of the ideal Whitehead graphs with a non trivial
        stabilizer. This allows to compute the index as the some of
        the number of vertices of connected components minus two (see
        also ``TrainTrackMap.index_lis()`` and
        ``TrainTrackMap.index()``).

        Vertices are equivalence classes of stable germs of the graph
        of ``self``. Two germs are equivalent if they are the end of a
        periodic Nielsen path. There is an edge between two such germs
        if the corresponding turn is used by the iterated images of
        edges. Of course only connected components with >2 vertices
        are considered.

        The germ of the edge 'a' is designated by 'a'. 

        For the two germs out of a periodic point inside an edge we
        use the notation:

        ``(e,period,left,right)``

        where the source of the germ is the fix point of f^period
        corresponding to the occurence of the edge e in the path
        f^period(e)=uev with left=len(u) and right=len(v). ``period``
        is chosen as small as possible to denote that periodic
        point. The germ is the one with the same orientation as ``e``.
        
        WARNING:
        
        If pnps is not given computes them by calling
        ``self.periodic_nielsen_paths()``. Thus it is assumed that
        ``self`` is an expanding train-track.

        Moreover the computation is not correct if there are periodic
        (infinite index) subgroups (eg: ``self`` is not irreducible or
        has closed Nielsen paths).

        SEE ALSO::

        TrainTrackMap.periodic_nielsen_loops()        
        """
        G=self.domain()
        A=G.alphabet()

        iwg=Graph(multiedges=False)

        germ_classes=[]
 
        if pnps is None:
            pnps=self.periodic_nielsen_paths(end_points=True,verbose=(verbose and verbose>1 and verbose-1))

        if verbose:
            print "Periodic Nielsen paths:"
            print pnps
        
        for ((u1,u2),period,(vv1,vv2)) in pnps:
            if len(vv1)==4: #vv1 is a germ in the middle of an edge: (a,period,left,right)
                v1=(A.inverse_letter(vv1[0]),vv1[1],vv1[3],vv1[2])
                iwg.add_edge((v1,vv1))
            if len(vv2)==4: #vv2 is a germ in the middle of an edge: (a,period,left,right)
                v2=(A.inverse_letter(vv2[0]),vv2[1],vv2[3],vv2[2])
                iwg.add_edge((v2,vv2))

            # build the germ classes of germs ending pnps

            if verbose:
                print "germs",vv1,"and",vv2,"are the ends of a pnp."

            for (j,c) in enumerate(germ_classes): 
                if vv1 in c:
                    i1=j
                    break
            else:
                i1=len(germ_classes)
                germ_classes.append([vv1])

            for (j,c) in enumerate(germ_classes):
                 if vv2 in c:
                     if j==i1:
                         break
                     else:
                         germ_classes[i1]=germ_classes[i1]+c
                         germ_classes.pop(j)
                         break
            else:
                germ_classes[i1].append(vv2)

        if verbose:
            print "Classes of germ at the end of pnps:",germ_classes
                
        for v in G.vertices():
            iwg=iwg.union(self.stable_local_whitehead_graph(v))
                       
        if verbose:
            print "Graph before identification of equivalent germs:", iwg.edges()

        # Now mod out the graph by inps

        for c in germ_classes:
            if len(c)>0:
                c0=c[0]
                if not len(c0)==4:
                    c0=c0[0]
                for i in xrange(1,len(c)):
                    ci=c[i]
                    if not len(ci)==4:
                        ci=ci[0]
                    for e in iwg.edges_incident(ci):
                        iwg.delete_edge(e)
                        if e[0]==ci:
                            iwg.add_edge((c0,e[1]))
                        else:
                            iwg.add_edge((e[0],c0))
                    iwg.delete_vertex(ci)

        # Add the loops to the corresponding connected components

        loops=self.periodic_nielsen_loops(pnps,verbose=(verbose and verbose>1 and verbose-1))

        for loop,vertex,period in loops:
            added=False
            for c in germ_classes:
                for germ in c:
                    if len(germ)==4:
                        if not A.is_positive_letter(germ[0]):
                            germ_vertex=(A.inverse_letter(germ[0]),germ[1],germ[3],germ[2])
                        else:
                            germ_vertex=germ
                    else:
                        germ_vertex=(G.initial_vertex(germ[0]),)
                    if vertex==germ_vertex:
                        if len(c[0])==1:
                            iwg.add_edge(c[0][0],'loop',None)
                            iwg.add_edge('loop',loop,None)
                        else:
                            iwg.add_edge(c[0],'loop',None)
                            iwg.add_edge('loop',loop,None)
                        added=True
                        break
                if added:
                    break

        return iwg
        
                    


    def index(self):
        """
        Stabilized index of ``self`` as defined by Gaboriau, Jaeger,
        Levitt and Lustig [GJLL].

        Let Phi be an outer automorphism of the free group of rank
        N. Let ind(Phi) be the GJLL index of Phi. This ind(Phi) is a
        positive integer or half a positive integer and it is bounded
        between 1/2 and N-1.

        The sequence ind(Phi^(n!)) is non-decreasing and eventually
        constant equal to what we call the stabilized index of Phi.
        
        The index and stabilized index of Phi are invariant of the
        conjugacy class of the outer automorphism Phi.
        
        ``self.index()`` is the stabilized index of the outer
        automorphism represented by Phi.

        This is the sum of the index list of ``self``. It can be
        computed using stable Whitehead graphs and Nielsen paths.

        WARNING: 

        calls ``self.ideal_whitehead_graph()`` and thus
        ``self.periodic_nielsen_paths()`` and thus assumes that
        ``self`` is an expanding train-track map.

        Moreover the computation is not correct if there are fixed
        subgroups (eg: ``self`` is not irreducible or has closed
        Nielsen loops).

        Some authors (Mosher, Pfaff), use -1/2 our index definition.

        Some authors (Gaboriau, Levitt), use 1/2 out index definition

        """

        return sum(self.index_list())

    def index_list(self,verbose=True):
        """Index list of ``self``.

        This index list is defined in [pfaff], this is the list of
        number of vertices of connected components of the ideal
        whitehead graph minus two.

        This is also the list of indices of singular non-isogredient
        automorphisms in the outer class of the outer automorphism
        represente by ``self``.

        WARNING: 

        calls ``self.ideal_whitehead_graph()`` and thus
        ``self.periodic_nielsen_paths()`` and thus assumes that
        ``self`` is an expanding train-track map.

        Some authors (Mosher, Pfaff), use -1/2 our index definition.

        Some authors (Gaboriau, Jaeger, Levitt,Lustig), use 1/2 our index definition

        REFERENCES:

        [GJLL] D. Gaboriau, A. Jaeger, G. Levitt, M. Lustig, An index
        for counting fixed points of automorphisms of free
        groups. Duke Math. J., 93(3):425-452, 1998.

        [HM-axes] M. Handel, L. Mosher, Axes in Outer Space, Memoirs
        AMS 1004, Amer Mathematical Society, 2011.

        [Pfaff] C. Pfaff, Out(F_3) Index realization, arXiv:1311.4490.

        """

        l=[len(c)-2 for c in self.ideal_whitehead_graph().connected_components()]
        return [i for i in l if i>0]

    def blow_up_vertices(self,germ_components):
        """
        Blow-up ``self`` according to classes of germs given in
        ``germ_components``.

        It is assumed that in the iterated images of an edge, two
        consecutive edges lie in the same class of germs.

        INPUT:

        ``germ_components`` a list of classes of germs outgoing from a
        vertex.

        OUTPUT:

        A WordMorphism that maps old edges to their fold image.

        EXAMPLE::

        sage: phi=FreeGroupAutomorphism("a->bca,b->bcacacb,c->cac")
        sage: f=TrainTrackMap(phi.rose_representative())
        sage: f.blow_up_vertices([['a', 'b', 'C'], ['A', 'c', 'B']])

        """
        G=self.domain()
        A=G.alphabet()

        edge_map=dict((a,self.image(a)) for a in A.positive_letters())

        blow_up_map=G.blow_up_vertices(germ_components)

        for c in germ_components:
            if A.is_positive_letter(c[0]):
                ec=blow_up_map[c[0]][0]
            else:
                ec=A.inverse_letter(blow_up_map[A.inverse_letter(c[0])][-1])
            f=self.image(c[0])[0]
            if A.is_positive_letter(f):
                fc=blow_up_map[f][0]
            else:
                fc=A.inverse_letter(blow_up_map[A.inverse_letter(f)][-1])
            edge_map[ec]=Word([fc])
                
        self.set_edge_map(edge_map)

        return WordMorphism(blow_up_map)


    def whitehead_connected_components(self,verbose=False):
        """
        List of connected components of local Whitehead graphs.

        The local Whitehead graph at a vertex ``v`` is the graph with
        vertices the germs of edges outgoing from ``v``. To such germs
        are linked by an edge if they appeart as a transition in the
        iterated image of an edge.

        OUTPUT:

        A list of list of edges. Each list is a connected
        component. Each edge stands for its starting germ.

        EXAMPLE::

        sage: phi=FreeGroupAutomorphism("a->bca,b->bcacacb,c->cac")
        sage: f=TrainTrackMap(phi.rose_representative())
        sage: f.whitehead_connected_components()

        SEE ALSO::

        TrainTrackMap.local_whitehead_graph()



        """
        G=self.domain()
        A=G.alphabet()
        
        component=dict((a,a) for a in A)

        for t in self.edge_turns():
            k=component[t[0]]
            kk=component[t[1]]
            if k!=kk:
                for b in A:
                    if component[b]==kk:
                        component[b]=k

        components=[]

        while len(component)>0:
            a,b=component.popitem()
            components.append([a])
            for c in component:
                if component[c]==b:
                    components[-1].append(c)
            for i in xrange(len(components[-1])-1):
                component.pop(components[-1][i+1])

        return components

    def periodic_point_normal_form(self,point,keep_orientation=False,verbose=False):
        """
        Normal form to denote periodic points of ``self`` inside
        edges.

        Intended to be used to compute the end points of periodic
        Nielsen paths.
        
        A periodic point of ``self`` inside an edge is denoted by
        ``(e,period,left,right)``. The point ``x`` is the unique point
        such that ``self^period(x)=x`` and ``x``lies in the occurences
        of ``e`` inside ``self^period(e)`` such that
        ``self^period(e)=uev`` with ``len(u)=left and len(v)=right``.

        The normal formal is the one that minimizes the period.

        if ``keep_orientation==False`` then returns that of
        ``(e,period,left,right)`` and ``(ee,peirod,right,left)``
        according to which of ``e`` or ``ee`` is a positive letter, where
        ``ee`` is the inverse letter of ``e``.

        OUTPUT:

        ``(e,period,left,right)`` denoting the same periodic point, but
        with the smallest period possible.

        INPUT:

        ``(e,period,left,right)`` standing for the periodic point x in
        the edge ``e`` with the given period.

        WARNING:

        If ``keep_orientation==True``, this is not exactly a normal
        form as each such periodic point has two normal forms:

        ``(e,period,left,right)`` and ``(ee,period,right,left)`` where
        ``ee`` is the inverse letter of ``e``.
        """
  
        A=self.domain().alphabet()

        (e,period,left,right)=point

        if verbose: print "Normal form of point",point

        simplified=False

        if period>1:
            M1=self.matrix()
            M=[M1**(i+1) for i in xrange(period)]
            left_ab_i=matrix(len(A),1)
            left_ab_period=left_ab_i
            left_length_period=0
            a=e
            for i in xrange(1,period):
                u=self(a)
                left_ab_i=M[0]*left_ab_i
                for a in u:
                    a_ab_i=M[0].matrix_from_columns([A.rank(A.to_positive_letter(a))])
                    a_ab_period=M[period-i-1]*a_ab_i
                    left_length_period=left_length_period+sum(a_ab_period)[0]
                    if left_length_period>left:
                        break
                    left_lenght_period=left_length_period+sum(a_ab_period)[0]
                    left_ab_period=left_ab_period+a_ab_period
                    left_ab_i=left_ab_i+a_ab_i
                if period%i==0 and a==e:
                    left_periodic_length=left_length_period+sum(left_ab_i)[0]
                    for k in xrange(1,period//i):
                        left_periodic_length=left_periodic_length+sum(M[k*i]*left_ab_i)[0]
                    if left_periodic_length==left:
                        if verbose: print "simplified to (",e,",",diviseur,",",i,")"
                        period=i
                        left=sum(left_ab_i)[0]
                        simplified=True
                        break 
                if verbose: print "no simplification with period=",i
                                     
        if simplified: #we need to compute right
            right=sum(M[period-1].column(A.rank(A.to_positive_letter(e))))-left-1

        A=self.domain().alphabet()
        if not keep_orientation and not A.is_positive_letter(e):
            e=A.inverse_letter(e)
            left,right=right,left
            
                
        return (e,period,left,right)


    def is_iwip(self,verbose=False):
        """
        ``True`` if ``self`` represents an iwip automorphism.

        ALGORITHM:

        1/ Try to reduce ``self`` (removing valence 1 or 2 vertices, invariant forests)

        3/ Check that the matrix has a power with strictly positive entries

        4/ Check the connectedness of local Whitehead graphs

        4/ Look for periodic Nielsen paths and periodic Nielsen loops.

        5/ If there are no periodic Nielsen loop then it is an
        atoroidal iwip [Kapo-algo]

        6/ If there is more than two Nielsen loops then it is not iwip

        7/ If there is one iwip check whether it is contained in a
        non-trivial free factor.

        REFERENCES

        [Kapo-algo] I. Kapovich, Algorithmic detectability of iwip
        automorphisms, 2012, arXiv:1209.3732
        """
        self.reduce(verbose and verbose>1 and verbose-1)
        if verbose:
            print "Reduced form:"
            print self
        if len(self._strata)>1:
            if verbose: 
                print "Reducible"
        if verbose:
            print "Irreducible train-track map"
        if not self.is_perron_frobenius():
            if verbose:
                print "Not fully irreducible: the matrix of self does not have a strictly positive power"
            return False
        if verbose:
            print "Fully irreducible: the matrix of self has a strictly positive power"
        c=self.whitehead_connected_components(verbose and verbose>1 and verbose-1)
        if len(c)>len(self.domain().vertices()):
            if verbose:
                print "The local Whitehead graphs are not connected. Connected components of germs:",c
            return False
        if verbose:
            print "Local Whitehead graphs are connected"
        pnps=self.periodic_nielsen_paths(end_points=True,verbose=verbose and verbose>1 and verbose-1)
        nielsen_loops=self.periodic_nielsen_loops(pnps,verbose=verbose and verbose>1 and verbose-1)
        if len(nielsen_loops)>0:
            if len(nielsen_loops)>1:
                if verbose:
                    print "There are more than two periodic Nielsen loops:",nielsen_loops
                return False
            else:
                if verbose:
                    print "One Nielsen loop:",nielsen_loops[0][0]
                if self.domain().lies_in_a_free_factor(nielsen_loops[0][0],verbose and verbose>1 and verbose-1):
                    if verbose:
                        print "The Nielsen loops is primitive"
                    return False
                else:
                    if verbose:
                        print "Geometric iwip"
                    return True
        else:
            if verbose:
                print "No Nielsen loops"
                print "Atoroidal iwip"
            return True
