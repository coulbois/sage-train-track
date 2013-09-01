#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
# 
#  Distributed under the terms of the GNU General Public License (GPL) 
#                  http://www.gnu.org/licenses/ 
#***************************************************************************** 

class TopologicalRepresentative(GraphMap):
    """
    A topological representative of an automorphism of a free group,
    is a marked graph together with a homotopy equivalence of this
    graph that induces the automorphism on the fundamental group.

    Here a TopologicalRepresentative is a GraphMap, with the Graph
    a MarkedGraph.

    Topological representative for an automorphism of free group can
    be created from the rose on the alphabet. They can also be created
    using the ``from_edge_map()`` method.

    EXAMPLES::

    sage: phi=FreeGroupAutomorphism("a->ab,b->ac,c->a",FreeGroup(3))
    sage: print phi.rose_representative()
    Graph with inverses: a: 0->0, b: 0->0, c: 0->0
    Marking: a->a, b->b, c->c
    Edge map: a->ab, b->ac, c->a

    sage: A=AlphabetWithInverses(5)
    sage: f=TopologicalRepresentative.from_edge_map("a->a,b->b,c->c,d->eCEAd,e->eCEAdbDaecEae",A)
    sage: print f
    Graph with inverses: a: 0->0, b: 2->2, c: 1->1, d: 0->2, e: 0->1
    Marking: a->a, b->dbD, c->ecE
    Edge map: a->a, b->b, c->c, d->eCEAd, e->eCEAdbDaecEae

    AUTHORS: 
 
    - Thierry Coulbois (2013-05-16): beta.0 version 
	 
    """


    def __init__(self,graph,edge_map,vertex_map=None):
        GraphMap.__init__(self,graph,graph,edge_map,vertex_map)
        self._strata=False

    def __str__(self):
        """
        String representation of ``self``.
        """
        result="Topological representative:\n"
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

    @staticmethod
    def from_edge_map(edge_map,alphabet=None,path=None):
        """
        Builds a topological representative from an edge map. 

        The graph is computed to be the biggest possible graph for
        which the edge_map is continuous. Additionnal information can
        be given in ``path``, the graph must admit ``path`` as an
        edge-path.

        The marking is chosen by picking a maximal forest in the graph
        and identifying the other edges, with generators of a free
        group.

        INPUT: 

        - ``edge_map`` a ``WordMorphism``, the letters must be from an
        ``AlphabetWithInverses``. Its is only required that images of
        positive letters are defined.

        - ``path`` (default None) an admissible edge-path in the base
          graph of the ``TopologicalRepresentatice``.

        EXAMPLES::

        sage: print TopologicalRepresentative.from_edge_map("a->a,b->b,c->c,d->eCEAd,e->dbDae")
        Topological representative:
        Graph with inverses: a: 0->0, b: 2->2, c: 1->1, d: 0->2, e: 0->1
        Marking: a->a, b->dbD, c->ecE
        Edge map: a->a, b->b, c->c, d->eCEAd, e->dbDae

        sage: print TopologicalRepresentative.from_edge_map("a->a,b->b,c->c,d->eCEAd,e->dbDae",path="ab")
        Topological representative:
        Graph with inverses: a: 0->0, b: 0->0, c: 1->1, d: 0->0, e: 0->1
        Marking: a->a, b->b, c->ecE, d->d
        Edge map: a->a, b->b, c->c, d->eCEAd, e->dbDae


        """

        edge_morph=WordMorphism(edge_map)
        if alphabet is None:
            alphabet=AlphabetWithInverses(edge_morph.domain().alphabet())
        equiv=dict((a,i) for i,a in enumerate(alphabet))

        # images of edges must be edge paths
        for a in edge_morph.domain().alphabet():
            w=edge_morph.image(a)
            for i in xrange(len(w)-1):
                x=alphabet.inverse_letter(w[i])                
                if equiv[x]!=equiv[w[i+1]]:
                    tmp=equiv[w[i+1]]
                    equiv[w[i+1]]=equiv[x]
                    for y in equiv:
                        if equiv[y]==tmp:
                            equiv[y]=equiv[x]
                
        # path must be an edge-path
        if path is not None:
            for i in xrange(len(path)-1):
                x=alphabet.inverse_letter(path[i])                
                if equiv[x]!=equiv[path[i+1]]:
                    tmp=equiv[path[i+1]]
                    equiv[path[i+1]]=equiv[x]
                    for y in equiv:
                        if equiv[y]==tmp:
                            equiv[y]=equiv[x]
              
        # the map must be continuous at vertices
        done=False
        while not done:
            done=True
            for i in xrange(len(alphabet)*2-1):
                for j in xrange(i+1,len(alphabet)*2):
                    a=alphabet[i]
                    b=alphabet[j]
                    if equiv[a]==equiv[b]:
                        if i<len(alphabet):
                            x=edge_morph.image(a)[0]
                        else:
                            x=alphabet.inverse_letter(edge_morph.image(alphabet.inverse_letter(a))[-1])
                        if j<len(alphabet):
                            y=edge_morph.image(b)[0]
                        else:
                            y=alphabet.inverse_letter(edge_morph.image(alphabet.inverse_letter(b))[-1])
                        if equiv[x]!=equiv[y]:
                            done=False
                            tmp=equiv[x]
                            equiv[x]=equiv[y]
                            for z in equiv:
                                if equiv[z]==tmp:
                                    equiv[z]=equiv[y]

        #Renumber vertices starting form 0
        vertex=0
        result=dict()
        for x in equiv:
            if equiv[x] not in result:
                result[equiv[x]]=vertex
                vertex+=1

        for x in equiv:
            equiv[x]=result[equiv[x]]

        result=dict((a,(equiv[a],equiv[alphabet.inverse_letter(a)])) for a in alphabet.positive_letters())

        G=GraphWithInverses(result,alphabet=alphabet)

        marked_G=MarkedGraph(G)
                
        
        return TopologicalRepresentative(G,edge_map)


    def matrix(self):
        """
        Incidence matrix of ``self``. 

        The indices of the matrix are determined by the order in the
        alphabet.
        """
        A=self._domain._alphabet
        m=len(A.positive_letters())
        M=matrix(m)
        for i,a in enumerate(A.positive_letters()):
            for b in self.image(a):
                M[A.rank(A.to_positive_letter(b)),i]+=1
        return M
     
    def expansion_factor(self,stratum=None):
        """
        The dominant Perron-Frobenius eigenvalue of the matrix of self.

        INPUT: 

        - ``stratum`` -- (default:None) if not None an integer
           that is the index of a stratum of self.

        """

        if stratum==None:
            eigenvalues=self.matrix().eigenvalues()
        else:
            eigenvalues=self.relative_matrix(stratum).eigenvalues()

        result=0
        for x in eigenvalues:
            if x in AA and x>result: result=x
        return result

    def automorphism(self,verbose=False):
        """
        Automorphism represented by ``self``.
        """

        if isinstance(self._domain,MarkedGraph):
            G=self._domain
        else:
            G=Marked_Graph(self._domain)
        A=G.marking().domain().alphabet()
        B=self._domain.alphabet()

        tree=self._domain.maximal_tree()
        if verbose: print "Spanning tree: ",tree
        rename_dict={}
        for a in tree:
            rename_dict[a]=Word([])
            rename_dict[B.inverse_letter(a)]=Word([])
        i=0
        for a in A.positive_letters():
            while B[i] in rename_dict: i=i+1
            rename_dict[B[i]]=Word([a])
            rename_dict[B.inverse_letter(B[i])]=Word([A.inverse_letter(a)])

        rename=WordMorphism(rename_dict)

        if verbose: print "Rename morphism: ",rename

        FA=FreeGroup(A)
        h=FreeGroupAutomorphism(rename*G.marking().edge_map(),group=FA).inverse()

        return FreeGroupAutomorphism(h*rename*self._edge_map*G.marking().edge_map(), group=FA)


    def find_folding(self):
        """
        Finds a folding in ``self``.

        OUTPUT:

        A list ``[[edge,position],t1,t2,...,tn]`` where ``tn`` is a
        fold turn turn (the images of its two edges have a non-trivial
        common prefix) that is in the iterated image of ``edge``
        (``self(ti)=ti+1``). The turn is chosen such as ``n`` is as
        small as possible. ``position`` is an integer such that ``t1``
        is the turn occuring at ``position`` in the word
        ``self(edge)``

        The empty list if ``self`` is train-track.

        """
        A=self._domain._alphabet
        turns=[]
        source={}
        for e in A.positive_letters(): # Builds the list of turns in the image of the edges
            w=self.image(e)
            for i in xrange(len(w)-1):
                x=A.inverse_letter(w[i])
                y=w[i+1]
                if A.less_letter(y,x): 
                    tmp=x
                    x=y
                    y=tmp
                if (x,y) not in turns:
                    turns.append((x,y))
                    source[(x,y)]=[[e,i+1]]
        done=False
        traintrack=True
        while not done:
            done=True
            new_turns=[]
            for t in turns: 
                tt=self.image_turn(t)
                if tt[0]==tt[1]:
                    fold=t
                    traintrack=False
                    done=True
                    break
                else:
                    if tt not in source: 
                        new_turns.append(tt)
                        source[tt]=source[t]+[t]
                        done=False
            turns=new_turns


        if traintrack: 
            return []
        else:
            return source[fold]+[fold]

    def subdivide(self,edge_list,verbose=False):
        """
        Subdivides edges into two edges. 

        If an edge appears in the list then

        - either len(self(edge))>1 and the first part of edge is sent
          to the first edge of the image.

        - or self(edge) is an edge in edge_list and the first part of
          edge is sent to the first part of its image.

        It is assumed that no edge and its reverse appear in the list.

        OUTPUT: 

        a WordMorphism that maps an old edge to its image in
        the subdivided graph.

        WARNING:

        this has no effect on the possible strata of self.
        """

        if verbose: print "Subdivide edges: ",edge_list

        subdivide_dict=self._domain.subdivide(edge_list)
        subdivide_morph=WordMorphism(subdivide_dict)

        result={}
        for e in self._edge_map.domain().alphabet():
            if len(subdivide_dict[e])==1:
                a=subdivide_dict[e][0]
                aa=self._domain._alphabet.inverse_letter(a)
                result[a]=subdivide_morph(self.image(e))
                result[aa]=self._codomain.reverse_path(result[a])

        for e in edge_list:
            a=subdivide_dict[e][0]
            b=subdivide_dict[e][1]
            if len(self.image(e))>1:
                result[a]=subdivide_dict[self.image(e)[0]]
                result[b]=subdivide_morph(self.image(e)[1:])
            else:
                result[a]=subdivide_dict[self.image(e)[0]][:1]
                result[b]=subdivide_dict[self.image(e)[0]][1:2]
                            
        self.set_edge_map(result)


        if verbose: print "\n",self

        return subdivide_morph

    def subdivide_edge(self,edge,position,verbose):
        """
        Subdivides ``edge`` in two edges a and b. The image of a is
        the prefix of length ``position`` of the image of ``edge``.

        OUTPUT:

        The WordMorphism for the old edges to the new images.

        WARNING:

        This has no effect on the possible strata of self.
        """
        
        if verbose:
            print "Subdivide edge: ",edge," at position ",position

        A=self._domain._alphabet

        subdivide_dict=self._domain.subdivide([edge])
        subdivide_morph=WordMorphism(subdivide_dict)

        result={}
        for e in self._edge_map.domain().alphabet():
            if len(subdivide_dict[e])==1:
                a=subdivide_dict[e][0]
                result[a]=subdivide_morph(self.image(e))

        a=subdivide_dict[edge][0]
        b=subdivide_dict[edge][1]
        result[a]=subdivide_morph(self.image(edge)[:position])
        result[b]=subdivide_morph(self.image(edge)[position:])
        aa=A.inverse_letter(a)
        bb=A.inverse_letter(b)
        result[aa]=self._domain.reverse_path(result[a])
        result[bb]=self._domain.reverse_path(result[b])
        
        self.set_edge_map(result)


        if verbose:
            print "\n",self

        return subdivide_morph

        


    def multifold(self,turns,verbose=False):
        """
        Folds (partially) and iteratively the turns
        
        INPUT:

        ``turns`` is a list ``[avoid,t1,t2,...,tn]`` with
        ``self(ti)=ti+1`` and ``t1`` is the image of
        ``avoid``. ``avoid`` is either a turn of the graph (a tuple of
        edges with common initial vertex) or a list
        ``[edge,position]`` which stands for the point at ``position``
        in ``edge``. Note that the two cases for ``avoid`` are
        discriminated by the fact that a turn is a tuple and
        ``[edge,position]`` a list.

        The folds are performed such that no branch-point will be
        created at ``avoid``.

        ``position`` is an integer meaning position/len(self(edge))
        assuming that self is linear on edges and that each edge has
        length 1.

        This is the induction step in the proof of Theorem 1.7 in
        [BH-train-track].

        WARNING:

        Beware this has no effect on the possible strata of self.

        REFERENCES:

        [BH-train-track] M. Bestvina, M. Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.

        
        """

        if verbose:
            print "Multifold: ",turns

        result_morph=False

        while len(turns)>1:
            
            if verbose:
                print "Safe Fold: ",turns[-1]," avoiding ",turns[0]

            turn=turns[-1]
            avoid=turns[0]

            u=self.image(turn[0])
            v=self.image(turn[1])

            prefix_length=self._domain.common_prefix_length(u,v)
            prefix=u[:prefix_length]

            partial=False

            if isinstance(avoid,list):
                position=avoid[1]
                edge=avoid[0]
                w=self.image(edge)


                redge=self._domain._alphabet.inverse_letter(edge)

                if (turn[0]==edge and position==prefix_length):
                    if prefix_length>1:
                        prefix_length=prefix_length-1
                    else:
                        partial=True
                elif (turn[0]==redge and len(w)-position==prefix_length):
                    if prefix_length>1:
                        prefix_length=prefix_length-1
                    else:
                        partial=True

                if not partial:
                    if turn[1]==edge and position==prefix_length:
                        if prefix_length>1:
                            prefix_length=prefix_length-1
                        else:
                            partial=True
                    elif turn[1]==redge and len(w)-position==prefix_length:
                        if prefix_length>1:
                            prefix_length=prefix_length-1
                        else:
                            partial=True


            else:
                avoid_vertex=self._domain.initial_vertex(turns[0][0])
                if prefix_length==len(u) and self._domain.terminal_vertex(turn[0])==avoid_vertex:
                    if prefix_length>1:
                        prefix_length=prefix_length-1
                    else:
                        partial=True
                if prefix_length==len(v) and self._domain.terminal_vertex(turn[1])==avoid_vertex:
                    if prefix_length>1:
                        prefix_length=prefix_length-1
                    else:
                        partial=True

            if partial:
                subdivide=[u[0]]

                done=False
                while not done:
                    done=True
                    x=self.image(subdivide[-1])
                    if len(x)==1: 
                        subdivide.append(x[0])
                        done=False
 
                if isinstance(avoid,list): avoid_image=w[0:position]

                subdivide_morph=self.subdivide(subdivide,verbose)

                if result_morph:
                    result_morph=subdivide_morph*result_morph
                else:
                    result_morph=subdivide_morph

                for i in xrange(1,len(turns)):
                    turns[i]=(subdivide_morph.image(turns[i][0])[0],subdivide_morph.image(turns[i][1])[0])
                prefix=subdivide_morph.image(subdivide[0])[0:1]

                if isinstance(avoid,list):
                    subdivide_avoid=subdivide_morph.image(avoid[0])
                    avoid_position=len(subdivide_morph(avoid_image))
                    k=1
                    while len(self(subdivide_avoid[0:k]))<avoid_position: k=k+1
                    avoid=subdivide_avoid[k-1]
                    if len(self(subdivide_avoid[0:k]))==avoid_position:
                        avoid=(self._domain.alphabet().inverse_letter(avoid),subdivide_avoid[k])
                    else:
                        avoid=[avoid,len(self(subdivide_avoid[0:k]))-avoid_position]
                else:
                    avoid=(subdivide_morph.image(avoid[0])[0],subdivide_morph.image(avoid[1])[0])

                turns[0]=avoid

            else:
                prefix=prefix[:prefix_length]

            fold_morph=self.fold(turns[-1],prefix,verbose=verbose)

            better=False #No edge in turns is mapped to a point.

            # update turns
            turns.pop()
            for i in xrange(1,len(turns)):
                u=fold_morph.image(turns[i][0])
                v=fold_morph.image(turns[i][1])
                if len(u)==0 or len(v)==0:
                    better=True
                    turns=turns[:i]
                    break
                elif u[0]==v[0]:
                    turns=turns[:i]
                    break
                else:
                    turns[i]=(u[0],v[0])

            if not better:
        
                while len(turns)>1 and turns[-1][0]==turns[-1][1]: turns.pop()

                if isinstance(turns[0],tuple):
                    if len(turns)==1:  # Tighten at the avoid vertex (which has valence 2)
                    
                        tighten_length=self._domain.common_prefix_length(self.image(turns[0][0]),self.image(turns[0][1]))
                        if tighten_length>0:  #not necessary ?
                            if verbose: print "Tighten at ",self._domain.initial_vertex(turns[0][0])
                            edge_map=dict((a,self.image(a)) for a in self._domain._alphabet)
                            a=turns[0][0]
                            b=turns[0][1]
                            aa=self._domain.alphabet().inverse_letter(a)
                            bb=self._domain.alphabet().inverse_letter(b)
                            edge_map[a]=edge_map[a][tighten_length:]
                            edge_map[b]=edge_map[b][tighten_length:]
                            edge_map[aa]=self._domain.reverse_path(edge_map[a])
                            edge_map[bb]=self._domain.reverse_path(edge_map[b])

                            self.set_edge_map(edge_map)

                            if verbose: print "\n",self

                    else:
                        u=fold_morph.image(turns[0][0])
                        v=fold_morph.image(turns[0][1])
                        if len(u)>0 and len(v)>0:
                            turns[0]=(u[0],v[0])
                        else:
                            turns=turns[:1] #this will stop the loop


                elif len(turns)>1:
                    b=self._domain.alphabet().inverse_letter(turns[1][0])
                    c=self._domain.alphabet().inverse_letter(turns[1][1])
                    done=False
                    for a in fold_morph.image(turns[0][0]):
                        if done: break
                        w=self.image(a)
                        for i in xrange(len(w)-1):
                            if (w[i]==b and w[i+1]==turns[1][1]) or (w[i]==c and w[i+1]==turns[1][0]):
                                turns[0]=[a,i+1]
                                done=True
                                break
                    if not done: #the avoid vertex is one of the extremities thus there was some folding in the avoid edge
                        turns=turns[:1] #We can stop the loop



            if result_morph:
                result_morph=fold_morph*result_morph
            else:
                result_morph=fold_morph

        return result_morph


    def fold(self,turn,common_prefix,verbose=False):
        """
        Folds the ``turn`` and identify the ``common_prefix`` of its image. 

        INPUT:

        - ``turn`` is a list of edges whose images by self share the common
        prefix. The first element of turn is allowed to be a tuple
        (path,'path') where path is a path in the graph of self which
        is mapped onto the ``common_prefix``.

        OUTPUT:

        A WordMorphism that maps old edges to their fold image.

        This is conform to the describtion of a fold in
        [BH-train-track].

        WARNING:

        Beware this has no effect on the possible strata of self.

        REFERENCES:

        [BH-train-track] M. Bestvina, M. Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.

        """

        A=self._domain.alphabet()

        if verbose:
            print "Fold: ",turn," common prefix ", common_prefix

        common_prefix_length=len(common_prefix)

        full_edges=[]
        partial_edges=[]
        l=1
        for e in turn:
            if isinstance(e,tuple) and e[1]=='path':
                full_edges.insert(0,e)
                l=len(e[0])
            elif len(self.image(e))==common_prefix_length:
                full_edges.append(e)
            else:
                partial_edges.append(e)

        fold_map=self._domain.fold(full_edges,partial_edges)
        fold_morph=WordMorphism(fold_map)

        edge_map={}
        if len(full_edges)==0:
            edge_map[fold_morph.image(partial_edges[0])[0]]=fold_morph(common_prefix)
        for e in partial_edges:
            if len(fold_morph.image(e))==2*l+1: # e and its inverse have been fold
                edge_map[fold_morph.image(e)[l]]=fold_morph(self.image(e)[common_prefix_length:-common_prefix_length])
            else:
                edge_map[fold_morph.image(e)[l]]=fold_morph(self.image(e)[common_prefix_length:])
        for e in fold_map:
            f=fold_map[e]
            if len(f)==1:
                f=f[0]
                edge_map[f]=fold_morph(self.image(e))

        self.set_edge_map(edge_map)

        if verbose: print "\n",self

        return fold_morph

    def fusion_lines(self,lines,target_edge_index=None,verbose=False):
        """
        Fusion each line of lines into a single edge. 

        If ``target_edge_index`` is ``None``, the isotopy is chosen such that
        the expansion factor does not grow, this requires that self is
        irreducible. Else, the isotopy is to the edge of index
        ``target_edge_index[i]`` for each ``lines[i]``.

        OUTPUT:

        The ``WordMorphism`` that maps the old edges to their images in the
        new graph.

        WARNING:

        This has no effect on the possible strata of self.
        """


        if verbose:
            print "Fusion lines: ", lines

        A=self._domain.alphabet()

        if not target_edge_index:
            target_edge_index=[0 for l in lines]
            least_vector_index=[A.rank(A.to_positive_letter(l[0])) for l in lines]
            M=self.matrix()
            vectors=M.eigenvectors_right()
            pf=0
            pfv=[]
            for (e,v,n) in vectors:
                if e in AA and e>pf: 
                    pfv=v[0]
                    pf=e
            for i in xrange(len(lines)):
                for j in xrange(len(lines[i])-1):
                    k=A.rank(A.to_positive_letter(lines[i][j+1]))
                    if pfv[k]<pfv[least_vector_index[i]]:
                        target_edge_index[i]=j+1
                        least_vector_index[i]=k

        if verbose: print "Keep edges: ",[line[target_edge_index[i]] for i,line in enumerate(lines)]

        edge_list=[lines[i][j] for i in xrange(len(lines)) for j in xrange(len(lines[i])) if j!=target_edge_index[i]]
        
        lines_image=[self(Word(line)) for line in lines]

        fusion_map=self._domain.contract_edges(edge_list)
        fusion_morph=WordMorphism(fusion_map)

        result_map={}

        for i in xrange(len(lines)):
            e=lines[i][target_edge_index[i]]
            a=fusion_map[e][0]
            result_map[a]=fusion_morph(lines_image[i])

        for a in self._edge_map.domain().alphabet():
            if len(fusion_map[a])>0:
                b=fusion_map[a][0]
                if b not in result_map and A.inverse_letter(b) not in result_map:
                    result_map[b]=fusion_morph(self.image(a))

        self.set_edge_map(result_map)


        if verbose: print "\n",self

        return fusion_morph



    def pretrivial_forest(self):
        """
        Returns the forest of edges which are mapped by a power of
        ``self`` to points.  

        OUTPUT:

        A list of trees, each tree is a list of edges.
        """
        A=self._domain.alphabet()
        pretrivial_edges=set(a for a in A.positive_letters() if len(self.image(a))==0)
        done=False
        while not done:
            done=True
            for a in A.positive_letters():
                if a not in pretrivial_edges:
                    if not any(A.to_positive_letter(b) not in pretrivial_edges for b in self.image(a)):
                        done=False
                        pretrivial_edges.add(a)
        forest=[]
        vertices=[]
        G=self._domain
        for e in pretrivial_edges:
            v=G.initial_vertex(e)
            vv=G.terminal_vertex(e)
            t=[i for i in xrange(len(forest)) if v in vertices[i] or vv in vertices[i]]
            if len(t)==0: 
                forest.append(set([e]))
                vertices.append(set([v,vv]))
            elif len(t)>0: 
                forest[t[0]].add(e)
                if len(t)==2:
                    forest[t[0]].update(forest[t[1]])
                    forest.pop(t[1])
                    vertices[t[0]].update(vertices[t[1]])
                    vertices.pop(t[1])
                else:
                    vertices[t[0]].update([v,vv])

        return forest

    def contract_invariant_forest(self,forest,verbose=False):
        """
        Contracts the invariant ``forest``. 

        ``forest`` is a list of list of edges. One list for each
        connected component.

        OUPUT:

        The WordMorphism that maps each old edge to its image.

        WARNING:

        This has no effect on the possible strata of self.
        """
        
        if verbose:
            print "Contract invariant forest: ",forest 
        
        contract_map=self._domain.contract_forest(forest)
        contract_morph=WordMorphism(contract_map)
        
        result_map=dict((contract_map[a][0],contract_morph(self.image(a))) for a in self._edge_map.domain().alphabet() if len(contract_map[a])==1)

        self.set_edge_map(result_map)
        
        if verbose: print "\n",self

        return contract_morph


    def maximal_filtration(self,verbose=False):
        """
        A maximal filtration of ``self``. 

        A filtration is a list of invariant set of edges.

        OUPUT:

        A list of sets of edges.  One set for each invariant non-empty
        subgraph, ordered from the smallest to the biggest.
        """
        A=self._domain._alphabet
        filtration=[set(A.positive_letters())]
        span=dict((a,set(A.to_positive_letter(b) for b in self.image(a))) for a in A.positive_letters())
        for a in A.positive_letters():
            span[a].add(a)
    
        done=False
        while not done:
            done=True
            for a in A.positive_letters():
                if len(span[a])<len(A):
                    q=set(c for b in span[a] for c in span[b])
                    if len(q)>len(span[a]):
                        span[a]=q
                        done=False
        done=False
        while not done:
            done=True
            union=set()
            for a in filtration[0]:
                q=union.union(span[a])
                if len(q)<len(filtration[0]):
                    union=q
            if len(union)>0:
                done=False
                filtration=[union]+filtration
    
        return filtration


    def contract_tails(self,tails,verbose=False):
        """
        Contracts the ``tails`` of ``self``. 

        INPUT:

        ``tails`` is a list of lists of edges. One list for each
        connected component.

        OUPUT:

        The WordMorphism that maps old edges to their images.
        
        WARNING:

        This has no effect on the possible strata of self.
        """

        if verbose:
            print "Contract tails: ", tails

        contract_map=self._domain.contract_forest(tails)
        contract_morph=WordMorphism(contract_map)

        result_map=dict((contract_map[a][0],contract_morph(self.image(a))) for a in self._edge_map.domain().alphabet() if len(contract_map[a])==1)

        self.set_edge_map(result_map)

        if verbose: print "\n",self

        return contract_morph

    def reduce(self,verbose=False):
        """
        Reduces ``self`` by: 

        1/ contract tails 

        2/ contract pretrivial forests
       
        3/ look for a maximal filtration

        4/ contract the lowest strata until the smallest invariant
        graph contains some loops. If this graph is not the whole
        graphs stratify self and returns.

        5/ fusion lines

        6/ contract pretrivial forests
       
        7/ look for a maximal filtration

        8/ contract the lowest strata until the smallest invariant
        graph contains some loops. If this graph is not the whole
        graphs stratify self.

        OUPUT:

        The WordMorphism that maps old edges to the new edges.
        """
        tails=self._domain.find_tails()
        if len(tails)>0:
            result_morph=self.contract_tails(tails,verbose)
        else: result_morph=False

        pretrivial_forest=self.pretrivial_forest()
        if len(pretrivial_forest)>0:
            tmp_morph=self.contract_invariant_forest(pretrivial_forest,verbose)

            if result_morph: 
                result_morph=tmp_morph*result_morph
            else:
                result_morph=tmp_morph

        filtration=self.maximal_filtration()
        if len(filtration)>1:
            i=0
            while i<len(filtration)-1 and len(self._domain.core_subgraph(filtration[i]))==0:
                i=i+1
            if i>0:
                trees=self._domain.connected_components(filtration[i-1])
                tmp_morph=self.contract_invariant_forest(trees,verbose)

                if result_morph: 
                    result_morph=tmp_morph*result_morph
                else:
                    result_morph=tmp_morph
                    
            if i<len(filtration)-1:
                self.stratify(verbose)
                if not result_morph:
                    result_morph=WordMorphism(dict((a,a) for a in self._domain._alphabet))
                return result_morph


        lines=self._domain.find_valence_2_vertices() 
        if len(lines)>0:
            tmp_morph=self.fusion_lines(lines,None,verbose)

            if result_morph: 
                result_morph=tmp_morph*result_morph
            else:
                result_morph=tmp_morph

            pretrivial_forest=self.pretrivial_forest()
            if len(pretrivial_forest)>0:
                result_morph=self.contract_invariant_forest(pretrivial_forest,verbose)*result_morph

            filtration=self.maximal_filtration()
            if len(filtration)>1:
                i=0
                while i<len(filtration)-1 and len(self._domain.core_subgraph(filtration[i]))==0:
                    i=i+1
                if i>0:
                    trees=self._domain.connected_components(filtration[i-1])
                    result_morph=self.contract_invariant_forest(trees,verbose)*result_morph

                    if result_morph: 
                        result_morph=tmp_morph*result_morph
                    else:
                        result_morph=tmp_morph
                    
        self.stratify(verbose)
            
        if not result_morph:
            result_morph=WordMorphism(dict((a,Word([a])) for a in self._domain._alphabet))

        return result_morph
            
    def _stabilize(self,verbose=False):
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


    def train_track(self,verbose=False):
        """ 
        Computes an absolute train-track representative for the
        automorphism defined by ``self`` or finds a reduction.

        ALGORITHM:

        * reduce ``self``, calling ``TopologicalRepresentative.reduce()``

        * look for a folding and fold it

        * go to 1.



        """
        done=False

        result_morph=self.reduce(verbose)

        if len(self._strata)>1: 
            if verbose: 
                print "Not irreducible"
                print self

            return result_morph

        while not done:
            if verbose: print self.expansion_factor()
            turns=self.find_folding()
            if len(turns)==0: 
                done=True
                if verbose:
                    print "Train-track !"
            else:
                self._strata=None
                tmp_morph=self.multifold(turns,verbose)
                result_morph=tmp_morph*result_morph
                

                tmp_morph=self.reduce(verbose)
                if tmp_morph:
                    result_morph=tmp_morph*result_morph
                
                done=len(self._strata)>1


        return result_morph

           
    def is_train_track(self,verbose=False):
        """
        ``True`` if ``self`` is a train-track representative.

        A topological representative is train-track if:

        * the graph is connected and does not contain vertices of
          valence 1 or 2.

        * it maps edges to non-trivial reduced
        edge-paths

        * there are no foldings in iterated images of edges.

        """

        G=self.domain()
        
        
        if len(G.connected_components(G.alphabet().positive_letters()))==1:
            if verbose:
                print "Connected graph"
        else:
            if verbose:
                print "Not connected"
            return False
            
        if len(G.find_tails())==0:
            if verbose:
                print "No vertices of valence 1"
        else:
            if verbose:
                print "There are vertices of valence 1"
            return False

        if len(G.find_valence_2_vertices())==0:
            if verbose:
                print "No vertices of valence 2"
        else:
            if verbose:
                print "There are vertices of valence 2"
            return False
        
        if len(self.find_folding())==0:
            print "No edge is fold under iterations\nTrain-track"
            return True
        else:
            print "There is an edge which is fold under iterations"
            return False
        

    def image_turn(self,t):
        """
        Image of the turn ``t``.
        
        INPUT:

        ``t`` is a couple ``(e,f)`` of edges, 

        OUTPUT:

        The image of this turn ``t``, that is to say the turn made of the
        first edges of self(e) and self(f). The resut turn is ordered
        with respect to the less_letter function of the alphabet.
        """
        e=self.image(t[0])[0]
        f=self.image(t[1])[0]
        if not self._domain._alphabet.less_letter(e,f):
            return (f,e)
        else:
            return (e,f)

    def edge_turns(self,stratum=None):
        """
        The set of turns that appear in the iterated image of
        edges. 

        If ``stratum`` is not ``None``, then returns the set of turns
        in ``stratum` that are in the iterated image of an edge of
        ``stratum``.
        """
        
        A=self._domain._alphabet
        result=set()
        new=[]

        if stratum==None:
            for a in A.positive_letters():
                u=self.image(a)
                for i in xrange(len(u)-1):
                    t=(A.inverse_letter(u[i]),u[i+1])
                    if not A.less_letter(t[0],t[1]):
                        t=(t[1],t[0])
                    if t not in result:
                        result.add(t)
                        new.append(t)

        else:
            for a in self._strata[stratum]:
                u=[b for b in self.image(a) if A.to_positive_letter(b) in self._strata[stratum]] 
                for i in xrange(len(u)-1):
                    t=(A.inverse_letter(u[i]),u[i+1])
                    if not A.less_letter(t[0],t[1]):
                        t=(t[1],t[0])
                    if t not in result:
                        result.add(t)
                        new.append(t)
                

        while len(new)>0:        
            t=new.pop()
            tt=self.image_turn(t)
            if tt not in result: 
                result.add(tt)
                new.append(tt)
        
        return result

    def legal_turns(self):
        """
        The list of legal turns of ``self``. 

        A turn is legal if all its iterated images are non-degenerate
        turns.
        """

        turns=self._domain.turns()
        done=False
        while not done:
            done=True
            i=0
            while i<len(turns):
                tt=self.image_turn(turns[i])
                if tt not in turns: 
                    turns.pop(i)
                    done=False
                else: 
                    i=i+1
        return turns

    def fold_turns(self,stratum=None):
        """
        The list of turns that are fold by ``self``. 

        A turn is fold if the images of its two edges have a common
        prefix. If ``stratum`` is not ``None`` only consider illegal turns
        in the stratum. 

        SEE ALSO:

        TopologicalRepresentative.illegal_turns()

        """

        A=self._domain._alphabet
        
        turns=self._domain.turns()

        fold_turns=[]

        for t in turns:
            if (stratum==None or (A.to_positive_letter(t[0]) in self._strata[stratum] \
                                 and A.to_positive_letter(t[1]) in self._strata[stratum]))\
                                 and self.image(t[0])[0]==self.image(t[1])[0]:
                fold_turns.append(t)

        return fold_turns
        
    def illegal_turns(self,stratum=None,iteration=False):
        """
        The list of illegal turns of self.

        OUPUT:

        If ``iteration`` is ``True`` returns a list ``[(t,iter)]``
        where ``t``is an illegal turn and ``iter`` the number of
        iterations of ``self`` required to fold ``t``.

        Else returns a list of turns.
        
        """
        
        A=self._domain.alphabet()
        
        turns=self._domain.turns()
        if stratum!=None:
            i=0
            while i<len(turns):
                t=turns[i]
                if (A.to_positive_letter(t[0]) not in self._strata[stratum] \
                                 or A.to_positive_letter(t[1]) not in self._strata[stratum]):
                    turns.pop(i)
                else:
                    i+=1

        illegal_turns=[self.fold_turns(stratum)]

        done=False
        while not done:
            done=True
            i=0
            new=[]
            while i<len(turns):
                t=turns[i]
                if t in illegal_turns[-1]:
                    turns.pop(i)
                else:
                    tt=self.image_turn(t)
                    if tt in illegal_turns[-1]:
                        new.append(tt)
                        done=False
                        turns.pop(i)
                    else:
                        i+=1
            if len(new)>0:
                illegal_turns.append(new)

        if iteration:
            illegal_turns=[(t,i+1) for i in xrange(len(illegal_turns)) for t in illegal_turns[i]]
        else:
            illegal_turns=[t for new in illegal_turns for t in new]

        return illegal_turns
        



    def indivisible_nielsen_paths(self,verbose=False):
        """
        The list of indivisible Nielsen paths of ``self``.

        WARNING:
        
        ``self`` is assumed to be an irreducible train-track
        representative (else use
        ``relative_indivisible_nielsen_paths()``)

        OUPUT:
        
        A list of INPs. Each INP is returned as a pair of word-paths, the fixed
        points lie inside the extremal edges of the words.

        SEE ALSO:

        ``TopologicalRepresentative.relative_indivisible_nielsen_paths()``
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
                
            elif G.is_prefix(tt[0],t[0]) and (G.is_prefix(t[1],tt[1]) or G.is_prefix(tt[1],t[1])):
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
    
    def periodic_nielsen_paths(self,verbose=False):
        """
        The list of periodic Nielsen paths. 

        ``self`` is assumed to be an irreducible train-track representative.

        OUTPUT:
        
        A list of tuples ``(word1,word2,period)``. The fixed points lie in the last edge
        of the two words.
        """

        G=self._domain
        A=G._alphabet

        result=[]
        image=[]
        next=[]
        iteration=[]

        extension=dict((a,[]) for a in A)

        edge_turns=self.edge_turns()
        for t in edge_turns:
            extension[A.inverse_letter(t[0])].append(t[1]) 
            extension[A.inverse_letter(t[1])].append(t[0])
          
        
        for t in self.illegal_turns(iteration=True):
            result.append((Word(),Word()))
            image.append((Word(),Word())) #tigthen image of result
            next.append(t[0]) #letters to add to result
            iteration.append(t[1])

        illegal_turns=next[:]
        illegal_iter=iteration[:]

        u=[None,None]
        uu=[None,None]
                     
        i=0
        while i<len(result):
            ot=result.pop(i)
            iter=iteration.pop(i)
            ott=image.pop(0)
            ext=next.pop(0)

            for j in xrange(2):
                if ext[j]!=None:
                    u[j]=ot[j]*Word([ext[j]])
                    uu[j]=ott[j]*self.image(ext[j],iter)
                else:
                    u[j]=ot[j]
                    uu[j]=ott[j]

            t=(u[0],u[1])
            p=G.common_prefix_length(uu[0],uu[1])                
            tt=(uu[0][p:],uu[1][p:])
            
            if verbose: print t[0],",",t[1],"iteration:",iter,"image:", tt[0],",",tt[1]

            if len(tt[0])==0:
                for a in extension[t[0][-1]]:
                    result.insert(i,t)
                    image.insert(0,tt)
                    next.insert(0,(a,None))
                    iteration.insert(i,iter)
                    
            elif len(tt[1])==0:
                for a in extension[t[1][-1]]:
                    result.insert(i,t)
                    image.insert(0,tt)
                    next.insert(0,(None,a))
                    iteration.insert(i,iter)

                                        
            elif (G.is_prefix(t[0],tt[0]) and G.is_prefix(t[1],tt[1])): 
                    result.insert(i,t)
                    iteration.insert(i,iter)

                    if verbose: print "inp"
                    i+=1
                
            elif G.is_prefix(tt[0],t[0]) and (G.is_prefix(t[1],tt[1]) or G.is_prefix(tt[1],t[1])):
                for a in extension[t[0][-1]]:
                    result.insert(i,t)
                    image.insert(0,tt)
                    next.insert(0,(a,None)) 
                    iteration.insert(i,iter)

            elif G.is_prefix(tt[1],t[1]) and G.is_prefix(t[0],tt[0]):
                for a in extension[t[1][-1]]:
                    result.insert(i,t)
                    image.insert(0,tt)
                    next.insert(0,(None,a)) 
                    iteration.insert(i,iter)

            else:
                ttt=(tt[0][0],tt[1][0])
                if A.less_letter(ttt[1],ttt[0]):
                    ttt=(ttt[1],ttt[0])
                    tt=(tt[0],tt[1])
                j=0
                found=False
                while not found and j<len(illegal_turns):
                    if ttt!=illegal_turns[j]:
                        j+=1
                    else: found=True
                if found:
                    l=0
                    found=False
                    while not found and l<i:
                        if G.is_prefix(result[l][0],tt[0]) and G.is_prefix(result[l][1],tt[1]):
                            found=True
                        else:
                            l+=1
                    if not found:
                        result.append(ot)
                        k=illegal_iter[j]
                        if len(ott[0])>0:
                            u[0]=self._edge_map(ott[0],k)
                        else: u[0]=Word()
                        if len(ott[1])>0:
                            u[1]=self._edge_map(ott[1],k)
                        else: u[1]=Word()
                        p=G.common_prefix_length(u[0],u[1])
                        image.append((u[0][p:],u[1][p:]))
                        next.append(ext)
                        iteration.append(iter+illegal_iter[j])


        return [(t,iter) for t,iter in zip(result,iteration)]


        
        
        

    def relative_indivisible_nielsen_paths(self,stratum=None,verbose=False):
        """
        The list of indivisible Nielsen paths of ``self`` that
        intersect the interior of the ``stratum`` of self. 

        Each INP is a pair ``(u,v)`` with the fixed points lying inside
        the last letters of ``u`` and ``v``.

        INPUT:

        ``stratum`` is the index of a stratum of ``self`` which is
        irreducible, exponential and satisfies the relative
        train-track conditions RTT-i, RTT-ii and RTT-iii. 
        """
        
        G=self._domain
        A=G._alphabet

        result=[]
        image=[]
        next=[]
        places=[] #To prevent infinite matching pseudo-paths
        
        extension=dict((a,[]) for a in self._strata[stratum])
        for a in self._strata[stratum]:
            extension[A.inverse_letter(a)]=[]

        edge_turns=self.edge_turns(stratum)
        for t in edge_turns:
            extension[A.inverse_letter(t[0])].append(t[1]) 
            extension[A.inverse_letter(t[1])].append(t[0])
                  
        fold_turns=self.fold_turns(stratum)
        for t in fold_turns:
            result.append((Word(),Word()))
            image.append((Word(),Word())) #tigthen image of result
            next.append((t[0],t[1])) #letters to add to result
            x=G.initial_vertex(t[0])
            places.append(set([(x,-1,x-1)]))

        u=[None,None]
        uu=[None,None]
                     
        i=0
        inp=0
        while i<len(result):
            t=result.pop(i)
            tt=image.pop(0)
            ext=next.pop(0)
            laces=places.pop(0)

            for j in xrange(2):
                if ext[j]!=None:
                    u[j]=t[j]*Word([ext[j]])
                    uu[j]=self.image(ext[j])
                else:
                    u[j]=t[j]
                    uu[j]=tt[j]

            t=(u[0],u[1])
            p=G.common_prefix_length(uu[0],uu[1])                
            tt=(uu[0][p:],uu[1][p:])
            
            if verbose: print t[0],t[1]," image: ", tt[0],",",tt[1]

            if len(tt[0])==0 and len(tt[1])==0:
                v0=G.terminal_vertex(t[0][-1])
                v1=G.terminal_vertex(t[1][-1])
                lace=(v0,0,v1,0)
                if lace not in laces:
                    for a in extension[t[0][-1]]:
                        for b in extension[t[1][-1]]:
                            v0=G.initial_vertex(a)
                            v1=G.initial_vertex(b)
                            laceab=(v0,-1,v1,-1)
                            if laceab not in laces:
                                laces=laces.copy()
                                laces.add(lace)
                                laces.add(laceab)
                                result.insert(i,t)
                                image.insert(0,tt)
                                next.insert(0,(a,b))
                                places.insert(0,laces)

            elif len(tt[0])==0:

                v0=G.terminal_vertex(t[0][-1])
                lace=(v0,0,t[1][-1],len(tt[1]))

                j=0
                while tt[1][j] not in extension: j=j+1
                tt=(tt[0],tt[1][j:])

                if lace not in laces:
                    for a in extension[t[0][-1]]:
                        v0=G.initial_vertex(a)
                        lacea=(v0,-1,t[1][-1],len(tt[1]))
                        if lacea not in laces:
                            result.insert(i,t)
                            image.insert(0,tt)
                            next.insert(0,(a,None))
                            laces=laces.copy()
                            laces.add(lace)
                            laces.add(lacea)
                            places.insert(0,laces)

                     
            elif len(tt[1])==0:

                v1=G.terminal_vertex(t[1][-1])
                lace=(t[0][-1],len(tt[0]),v1,0)

                j=0
                while tt[0][j] not in extension: j=j+1
                tt=(tt[0][j:],tt[1])

                if lace not in laces:
                    for a in extension[t[1][-1]]:
                        v1=G.initial_vertex(a)
                        lacea=(t[0][-1],len(tt[0]),v1,-1)
                        result.insert(i,t)
                        image.insert(0,tt)
                        next.insert(0,(None,a))
                        places.insert(0,laces)

            elif tt[0][0] in extension and tt[1][0] in extension:
                for j in xrange(2):
                    uu[j]=Word([a for a in tt[j] if a in extension])
                tt=(uu[0],uu[1])
                  
                if (G.is_prefix(t[0],tt[0]) and G.is_prefix(t[1],tt[1])): 
                    result.insert(i,t)
                    if verbose: print "possible inp"
                    i+=1
                    inp+=1
                
            elif G.is_prefix(tt[0],t[0]) and (G.is_prefix(t[1],tt[1]) or G.is_prefix(tt[1],t[1])):
                for a in extension[t[0][-1]]:
                    result.insert(i,t)
                    image.insert(0,tt)
                    next.insert(0,(a,None)) 
                    i+=1

            elif G.is_prefix(tt[1],t[1]) and G.is_prefix(t[0],tt[0]):
                for a in extension[t[1][-1]]:
                    result.insert(i,t)
                    image.insert(0,tt)
                    next.insert(0,(None,a))
                    i+=1

        while inp<len(result):
            t=result.pop(inp)
            tt=image.pop(0)
            ext=next.pop(0)
            for j in xrange(2):
                if ext[j]!=None:
                    u[j]=t[j]*Word(ext[j])
                    uu[j]=tt[j]*Word([a for a in self.image(ext[j]) if a in extension])
                else:
                    u[j]=t[j]
                    uu[j]=tt[j]

            t=(u[0],u[1])
            tt=(uu[0],uu[1])

            if (G.is_prefix(t[0],tt[0]) and G.is_prefix(t[1],tt[1])): 
                result.insert(inp,t)
                if verbose: print "inp"
                inp+=1
                
            elif G.is_prefix(tt[0],t[0]) and (G.is_prefix(t[1],tt[1]) or G.is_prefix(tt[1],t[1])):
                for a in extension[t[0][-1]]:
                    result.insert(inp,t)
                    image.insert(0,tt)
                    next.insert(0,(a,None)) 

            elif G.is_prefix(tt[1],t[1]) and G.is_prefix(t[0],tt[0]):
                for a in extension[t[1][-1]]:
                    result.insert(inp,t)
                    image.insert(0,tt)
                    next.insert(0,(None,a)) 
          
        if verbose: print "Possible INPs to be extended below stratum",stratum,":",result

        #add the connecting subpaths below stratum in the INPs
        i=0
        while i<len(result):
            t=result[i]
            if verbose: print "Extending below stratum",stratum,"possible inp",t
            u=Word([a for b in t[0] for a in self.image(b) if a in extension])
            v=Word([a for b in t[1] for a in self.image(b) if a in extension])
            p=G.common_prefix_length(u,v)
            tt=(u[p:],v[p:])
            new_t=[]
            for j in xrange(2):
                a=t[j][-1:]
                s_len_a=1
                post_s_len=len(tt[j])-len(t[j])
                while s_len_a<len(t[j]):
                    a=self(a)
                    post_s_len_a=0
                    s_len_a=1
                    len_a=1
                    k=0
                    prefix_len_a=-1
                    while post_s_len_a<=post_s_len:
                        if A.to_positive_letter(a[-k-1]) in self._strata[stratum]:
                            post_s_len_a+=1
                        k+=1

                    while k<len(a):
                        len_a+=1
                        if A.to_positive_letter(a[-k-1]) in self._strata[stratum]:
                            s_len_a+=1
                        if s_len_a>=len(t[j]):
                            prefix_len_a+=1
                        k+=1
                    a=a[prefix_len_a:len_a]
                new_t.append(a)
            u=self(new_t[0])
            v=self(new_t[1])
            p=G.common_prefix_length(u,v)
            tt=(u[p:],v[p:])
            if (G.is_prefix(new_t[0],tt[0]) and G.is_prefix(new_t[1],tt[1])):
                if verbose: print "INP:",new_t
                result[i]=new_t
                i+=1
            else:
                result.pop(i)

        return result
        





    def fold_inp_in_relative_train_track(self,inp,s,verbose=False):
        """
        Recursively fold the non-essential ``inp`` of the stratum
        ``s`` of ``self``.
        
        Assuming that self is a relative train-track and inp is a
        non-essential INP of the s stratum of self, recursively folds
        the inp until a partial fold occurs and the inp is removed.

        INPUT:

        ``inp`` is a couple ``(word1,word2)`` coding an INP of ``self``.

        OUTPUT:

        The ``WordMorphism`` from the old edges to new graph.

        """
        
        G=self._domain
        A=G.alphabet()
        stratum=set(e for e in self._strata[s])
        strata=self._strata
        self._strata=False

        result_morph=False

        done=False
        while not done:
            done=True
            if verbose: 
                print "Fold inp: ",inp[0],inp[1]
            image=(self.image(inp[0][0]),self.image(inp[1][0]))
            prefix_length=self._domain.common_prefix_length(image[0],image[1])
            if len(image[0])==prefix_length or len(image[1])==prefix_length:
                if verbose: print "Full fold"
                done=False

                if len(image[1])>len(image[0]): #order the two branches of the inp
                    inp=(inp[1],inp[0])  
                    image=(image[1],image[0]) # now image[0]>=image[1]

                if len(image[0])==prefix_length: #both edges have the same image
                    folding_morph=self.fold([inp[0][0],inp[1][0]],image[0],verbose=verbose)

                else: # now image[0]>image[1]
                    i=1
                    while A.to_positive_letter(inp[1][i]) not in stratum: i+=1
                    if i>1:
                        folding_morph=self.fold([(inp[1][:i],'path'),inp[0][0]],self(inp[1][:i]),verbose)
                    else:
                        folding_morph=self.fold([inp[0][0],inp[1][0]],image[1],verbose)

                stratum=set(A.to_positive_letter(folding_morph.image(a)[0]) for a in stratum) 
                stratum.add(A.to_positive_letter(folding_morph.image(inp[0][0])[-1]))

                inp=(folding_morph(inp[0]),folding_morph(inp[1]))
                prefix_length=self._domain.common_prefix_length(inp[0],inp[1])
                inp=(inp[0][prefix_length:],inp[1][prefix_length:])

                if result_morph:
                    result_morph=folding_morph*result_morph
                else:
                    result_morph=folding_morph

            else:  
                if verbose: print "Partial fold:",inp

                folding_morph=self.fold((inp[0][0],inp[1][0]),image[0][:prefix_length],verbose)

                edge_map=dict((a,self.image(a)) for a in A)

                u=folding_morph.image(inp[0][0])
                edge_map[u[0]]=self.image(u[0])*u[:1]
                edge_map[A.inverse_letter(u[0])]=G.reverse_path(edge_map[u[0]])
                if len(u)==2:
                    edge_map[u[1]]=self.image(u[1])[1:]
                    edge_map[A.inverse_letter(u[1])]=G.reverse_path(edge_map[u[1]])
                    v=folding_morph.image(inp[1][0])
                    edge_map[v[1]]=self.image(v[1])[1:]
                    edge_map[A.inverse_letter(v[1])]=G.reverse_path(edge_map[v[1]])
                else: #the INP is in a one-edge loop
                    edge_map[u[1]]=self.image(u[1])[1:-1]
                    edge_map[A.inverse_letter(u[1])]=G.reverse_path(edge_map[u[1]])
                   
                    
                self.set_edge_map(edge_map)
                   
                if result_morph:
                    result_morph=folding_morph*result_morph
                else:
                    result_morph=folding_morph
                
                if verbose: print "\n",self

        self._strata=strata
        return result_morph

        

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
                for i in xrange(2):
                    if len(self.image(inp[i][0]))==prefix_length+1:
                        full_edges.append(inp[i][0])
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

    def is_exponential_stratum(self,i):
        """
        ``True`` if the stratum ``i`` of ``self`` is exponential. 

        It is assumed that this stratum is irreducible.
        """

        M=self.relative_matrix(i)
        for l in M:
            m=0
            for c in l:
                m+=c
            if m>1: return True
        return False

    def relative_matrix(self,s):
        """
        The incidence matrix of the stratum ``i`` of ``self``.
        """

        M=matrix(len(self._strata[s]))
        index=dict((a,j) for j,a in enumerate(self._strata[s]))
        for j,a in enumerate(self._strata[s]):
            for b in self.image(a):
                b=self._domain._alphabet.to_positive_letter(b)
                if b in self._strata[s]:
                    M[index[b],j]+=1
        return M
   
    def filtre_stratum(self,s,verbose=False):
        """
        Refine the filtration by subdividing the stratum ``s`` into
        irreducible strata.  

        OUTPUT: 

        The number of strata which replaces the ``s`` stratum.
        """

        stratum=self._strata[s]
        if len(stratum)==0: 
            self._strata.pop(s)
            return 0
        A=self._domain._alphabet

        span=dict((a,set([a]+[A.to_positive_letter(b) for b in self.image(a)]).intersection(stratum)) for a in stratum)
        done=False
        while not done:
            done=True
            for a in stratum:
                if len(span[a])<len(stratum):
                    image=set([c for b in span[a] for c in span[b]])
                    if len(image)>len(span[a]): 
                        span[a]=image
                        done=False
        filtration=[stratum]
        done=False
        while not done:
            done=True
            smaller=set()
            for a in filtration[0]:
                tmp=smaller.union(span[a])
                if len(tmp)<len(filtration[0]):
                    smaller=tmp
            if len(smaller)>0:
                done=False
                filtration.insert(0,smaller)
        self._strata[s]=filtration[0]
        for i in xrange(1,len(filtration)):
            self._strata.insert(s+i,filtration[i].difference(filtration[i-1]))
        return len(filtration)

    def stratify(self,verbose=False):
        """
        Computes a maximal filtration for ``self`` and sets and the strata of ``self``.

        ``filtration`` if a list of invariant subgraphs of ``self``with
        ``filtration[i]`` a subgraph of ``filtration[i+1]``. The subgraphs
        ``filtration[i]`` are given as lists of edges.

        The ``i`` stratum is the set of edges that are in ``filtration[i]``
        and not in ``filtration[i-1]``.


        OUTPUT:

        The maximal filtration as a list of sets.

        SEE ALSO:

        ``TopologicalRepresentative.maximal_filtration()``
        """

        filtration=self.maximal_filtration(verbose)

        strata=[filtration[0]]
        for i in xrange(1,len(filtration)):
            strata.append(set(e for e in filtration[i] if e not in filtration[i-1]))
        self._strata=strata

        return filtration

    def update_strata(self,morph=None,verbose=False):
        """
        First applies ``morph`` (if present) to the strata of ``self``, then refine this
        filtration.  

        INPUT:

        ``morph``: a WordMorphism to be applied to the strata of ``self``.

        OUTPUT:

        a dictionnary that maps the index of an old strata ``s`` to the
        indices of the new strata that inherit from ``s``.
        """

        A=self._domain.alphabet()

        #Apply morph to the strata
        if morph:
            below=set()
            for s in xrange(len(self._strata)):
                self._strata[s]=set(A.to_positive_letter(a) for b in self._strata[s] for a in morph.image(b))
                self._strata[s].difference_update(below)
                below.update(self._strata[s])

        heritage={}

        result_strata=[]
        shift=0
        for s in xrange(len(self._strata)):
            n=self.filtre_stratum(s+shift,verbose)
            heritage[s]=[s+shift+i for i in xrange(n)]
            shift+=n-1
            
        if verbose: 
            if (morph or shift>0): 
                print "Updated strata: ",self._strata
            else:
                print "Strata are up-to-date."

        return heritage

    def find_relative_folding(self,s,verbose=False):
        """
        Finds an illegal turn of the ``i`` stratum of ``self`` in the
        image of an edge of the ``i`` stratum.

        INPUT:

        ``s``: the index of a stratum of ``self`` (0 is the bottom stratum)

        OUTPUT:

        A list ``[[edge,position],t1,t2,...,tn]`` where ``tn`` is a
        folded turn that is in the iterated image of ``edge`` (and
        ``self(ti)=ti+1``). The turn is chosen such as n is as small
        as possible.

        If the ``s`` stratum of ``self`` satisfies RTT-iii, returns an empty list.

        """
        A=self._domain.alphabet()
        turns=[]
        source={}
        for e in self._strata[s]: # Builds the list of turns in the image of the edges
            w=self.image(e)
            i=0
            while i<len(w)-1:
                if A.to_positive_letter(w[i]) not in self._strata[s]: 
                    i=i+1
                elif A.to_positive_letter(w[i+1]) not in self._strata[s]: 
                    i=i+2
                else:
                    x=A.inverse_letter(w[i])
                    y=w[i+1]
                    if A.less_letter(y,x): 
                        tmp=x
                        x=y
                        y=tmp
                        if (x,y) not in turns:
                            turns.append((x,y))
                            source[(x,y)]=[[e,i+1]]
                    i=i+1
        done=False
        traintrack=True
        while not done:
            done=True
            new_turns=[]
            for t in turns: 
                tt=self.image_turn(t)
                if A.to_positive_letter(tt[0]) in self._strata[s]:
                    if tt[0]==tt[1]:
                        fold=t
                        traintrack=False
                        done=True
                        break
                    elif tt not in source and A.to_positive_letter(tt[1]) in self._strata[s]: 
                        new_turns.append(tt)
                        source[tt]=source[t]+[t]
                        done=False
            turns=new_turns


        if traintrack: 
            return []
        else:
            return source[fold]+[fold]


    def core_subdivide(self,s,verbose):
        """
        Core subdivision of the ``s`` stratum of ``self`` as defined in [BH-train-track].

        After a core subdivision, the topological representative
        satisfies RTT-i: the image of each edge of the ``i`` stratum
        starts with an edge of the stratum.

        INPUT:

        ``s``: index of a stratum of ``self``.

        OUTPUT:

        The WordMorphism that maps old edges to their images.

        REFERENCES:

        [BH-train-track] M. Bestvina, M. Handel, Train tracks and
        automorphisms of free groups, Annals of Math, 135, 1-51, 1992.

        """

        A=self._domain.alphabet()
        Dfinverse=dict((e,[]) for e in self._strata[s])
        subdivide=[]

        for e in self._strata[s]:
            Dfinverse[A.inverse_letter(e)]=[]

        for e in self._strata[s]:
            f=self.image(e)[0]
            if f in Dfinverse:
                Dfinverse[f].append(e)
            else:
                subdivide.append(e)
            ee=A.inverse_letter(e)
            ff=self.image(ee)[0]
            if ff in Dfinverse:
                Dfinverse[ff].append(ee)
            else:
                subdivide.append(ee)

        new=subdivide[:]
        while len(new)>0:
            nnew=[]
            for e in new:
                for f in Dfinverse[e]:
                    subdivide.append(f)
                nnew=nnew+Dfinverse[e]
            new=nnew

        subdivide_inverse=[A.inverse_letter(a) for a in subdivide]

        if len(subdivide)>0:
            if verbose: print "Core subdivision of stratum",s,": subdivide edges: ",subdivide
            subdivide_map=self._domain.subdivide(subdivide)
            subdivide_morph=WordMorphism(subdivide_map)

            edge_map={}

            for e in self._strata[s]:

                if e in subdivide and e in subdivide_inverse:
                    w=self.image(e)
                    i=0
                    while w[i] not in Dfinverse: i=i+1     
                    j=len(w)-1
                    while w[j] not in Dfinverse: j=j-1

                    a=subdivide_map[e][0]
                    b=subdivide_map[e][1]
                    c=subdivide_map[e][2]
                    
                    edge_map[a]=subdivide_morph(w[:i])                
                    edge_map[b]=subdivide_morph(w[i:j+1])
                    edge_map[c]=subdivide_morph(w[j+1:])

                    if w[i] in subdivide:
                        edge_map[a]=edge_map[a]*subdivide_map[w[i]][0:1]
                        edge_map[b]=edge_map[b][1:]

                    if w[j] in subdivide_inverse:
                        edge_map[c]=subdivide_map[w[j]][-1:]*edge_map[c]
                        edge_map[b]=edge_map[b][:-1]
 
                elif e in subdivide:
                    w=self.image(e)
                    i=0
                    while w[i] not in Dfinverse: i=i+1    

                    a=subdivide_map[e][0]
                    b=subdivide_map[e][1]
                    
                    edge_map[a]=subdivide_morph(w[:i])                
                    edge_map[b]=subdivide_morph(w[i:])

                    if w[i] in subdivide:
                        edge_map[a]=edge_map[a]*subdivide_map[w[i]][0:1]
                        edge_map[b]=edge_map[b][1:]
 
                elif e in subdivide_inverse:
                    w=self.image(e)
                    j=len(w)-1
                    while w[j] not in Dfinverse: j=j-1

                    a=subdivide_map[e][0]
                    b=subdivide_map[e][1]
                    
                    edge_map[a]=subdivide_morph(w[:j+1])                
                    edge_map[b]=subdivide_morph(w[j+1:])


                    if w[j] in subdivide_inverse:
                        edge_map[a]=edge_map[a][:-1]
                        edge_map[b]=subdivide_map[w[j]][-1:]*edge_map[b]

                else:
                    edge_map[subdivide_map[e][0]]=subdivide_morph(self.image(e))

            for i in xrange(len(self._strata)):
                if i!=s:
                    for e in self._strata[i]:
                        edge_map[subdivide_map[e][0]]=subdivide_morph(self.image(e))

            self.set_edge_map(edge_map)


            for i in xrange(len(self._strata)):
                if i!=s:
                    self._strata[i]=set(subdivide_map[e][0] for e in self._strata[i])

            self._strata.insert(s,[])
            stratum_s=[]

            for e in self._strata[s+1]:

                if e in subdivide and e in subdivide_inverse:
                    self._strata[s].append(A.to_positive_letter(subdivide_map[e][0]))
                    self._strata[s].append(A.to_positive_letter(subdivide_map[e][2]))
                    stratum_s.append(A.to_positive_letter(subdivide_map[e][1]))
                elif e in subdivide:
                    self._strata[s].append(A.to_positive_letter(subdivide_map[e][0]))
                    stratum_s.append(A.to_positive_letter(subdivide_map[e][1]))
                elif e in subdivide_inverse:
                    self._strata[s].append(A.to_positive_letter(subdivide_map[e][1]))
                    stratum_s.append(A.to_positive_letter(subdivide_map[e][0]))
                else:
                    stratum_s.append(subdivide_map[e][0])

            self._strata[s]=set(self._strata[s])
            self._strata[s+1]=set(stratum_s)


            # Subdivide strata[s] into irreducible substrata:
            self.filtre_stratum(s,verbose)

            if verbose: print "\n",self

        else:
            if verbose:
                print "Stratum",s,"satisfies RTT-i (no need of core subdivision)."
            subdivide_morph=WordMorphism(dict((a,Word([a])) for a in self._domain._alphabet))
        return subdivide_morph

    def stratum(self,e):
        """
        The stratum of ``self`` that contains the edge ``e``.
        """
        e=self._domain.alphabet().to_positive_letter(e)
        for s,stratum in enumerate(self._strata):
            if e in stratum: return s
        raise ValueError("%s not in alphabet"%e)


    def relative_contract_tails_and_forest(self,verbose=False):
        """
        Reduces ``self`` by:

        1/ contract tails

        2/ contract pretrivial forests
        
        3/ contract lowest strata that are forest.
 
        4/ Update the maximal filtration encoded in self._strata.

        OUTPUT:

        The WordMorphism that maps an old edge to a new edge.

        """
        
        if verbose: 
            print "Contraction of tails and inviariant forest."

        #Contract tails

        tails=self._domain.find_tails()
        if len(tails)>0:
            result_morph=self.contract_tails(tails,verbose)
        else: result_morph=False

        #Contract pretrivial forest

        pretrivial_forest=self.pretrivial_forest()
        if len(pretrivial_forest)>0:
            tmp_morph=self.contract_invariant_forest(pretrivial_forest,verbose)
            if result_morph: 
                result_morph=tmp_morph*result_morph
            else:
                result_morph=tmp_morph

        #Contract invariant forest. 

        if len(self._strata)>1:
            i=0
            vertex_components=[]
            done=False
            while i<len(self._strata)-1 and not done:
                for a in self._strata[i]:
                    v=self._domain.initial_vertex(a)
                    vv=self._domain.terminal_vertex(a)
                    if v==vv:
                        done=True
                        break
                    cv=-1
                    cvv=-1
                    for j,component in enumerate(vertex_components):
                        if v in component: cv=j
                        if vv in component: cvv=j
                    if cv==-1 and cvv==-1:
                        vertex_components.append(set([v,vv]))
                    elif cv==-1:
                        vertex_components[cvv].add(v)
                    elif cvv==-1:
                        vertex_components[cv].add(vv)
                    elif cv!=cvv:
                        vertex_components[cv].update(vertex_components[cvv])
                        vertex_components.pop(cvv)
                    else:
                        done=True
                        break
                if not done:
                    i=i+1
            if i>0:
                trees=self._domain.connected_components([a for j in xrange(i) for a in self._strata[j]])
                tmp_morph=self.contract_invariant_forest(trees,verbose)
                self._strata=self._strata[i:]
                heritage=self.update_strata(tmp_morph,verbose)
                                    
                if result_morph: 
                    result_morph=tmp_morph*result_morph
                else:
                    result_morph=tmp_morph

        if not result_morph:
            result_morph=WordMorphism(dict((a,a) for a in self._domain._alphabet))

        return result_morph


    def relative_reduce(self,safe_strata=None,verbose=False):
        """
        Reduces self by:

        1/ contract tails

        2/ contract pretrivial forests
        
        3/ contract lowest strata that are forest.

        4/ Perform safe fusion of valence 2 vertices. The isotopy is
        chosen such that the expansion factors of self do not increase
        and (TODO: so that property RTT-i (no need of core
        subdivision) is not broken). A fusion is safe if either:
        
        - the upper most stratum contains only one edge of the fusion
          line

        or
        
        - the upper most stratum is not exponential

        or

        - the upper most stratum is exponential and one of the
        safe_strata and the fusion is towards one of the edges
        corresponding to the minimum coefficient of the right
        Perron-Frobenius eigen-vector.

        5/ contract pretrivial forests

        6/ Update the maximal filtration encoded in self._strata.

        OUTPUT:

        The WordMorphism that maps an old edge to a new edge.

        """
        
        if verbose: 
            if safe_strata:
                print "Relative reduction with safe strata ",safe_strata
            else:
                print "Relative reduction"

        #Contract tails

        tails=self._domain.find_tails()
        if len(tails)>0:
            result_morph=self.contract_tails(tails,verbose)
        else: result_morph=False

        #Contract pretrivial forest

        pretrivial_forest=self.pretrivial_forest()
        if len(pretrivial_forest)>0:
            tmp_morph=self.contract_invariant_forest(pretrivial_forest,verbose)
            if result_morph: 
                result_morph=tmp_morph*result_morph
            else:
                result_morph=tmp_morph

        heritage=self.update_strata(result_morph,verbose)
        if safe_strata:
            safe_strata=[i for s in safe_strata for i in heritage[s]]

        #Contract invariant forest. 

        if len(self._strata)>1:
            i=0
            vertex_components=[]
            done=False
            while i<len(self._strata)-1 and not done:
                for a in self._strata[i]:
                    v=self._domain.initial_vertex(a)
                    vv=self._domain.terminal_vertex(a)
                    if v==vv:
                        done=True
                        break
                    cv=-1
                    cvv=-1
                    for j,component in enumerate(vertex_components):
                        if v in component: cv=j
                        if vv in component: cvv=j
                    if cv==-1 and cvv==-1:
                        vertex_components.append(set([v,vv]))
                    elif cv==-1:
                        vertex_components[cvv].add(v)
                    elif cvv==-1:
                        vertex_components[cv].add(vv)
                    elif cv!=cvv:
                        vertex_components[cv].update(vertex_components[cvv])
                        vertex_components.pop(cvv)
                    else:
                        done=True
                        break
                if not done:
                    i=i+1
            if i>0:
                trees=self._domain.connected_components([a for j in xrange(i) for a in self._strata[j]])
                tmp_morph=self.contract_invariant_forest(trees,verbose)
                self._strata=self._strata[i:]
                heritage=self.update_strata(tmp_morph,verbose)

                
                if safe_strata:  
                    new_safe_strata=[]
                    for s in safe_strata:
                        if s>=i:
                            new_safe_strata+=heritage[s-i]
                    safe_strata=new_safe_strata
                                    
                if result_morph: 
                    result_morph=tmp_morph*result_morph
                else:
                    result_morph=tmp_morph

        #Fusion valence 2 vertices

        lines=self._domain.find_valence_2_vertices()

        if len(lines)>0:
            if verbose: print "Lines with valence 2 vertices: ",lines

            #Look for edges in the highest stratum of each line

            highest_edges=[[0] for line in lines]            
            highest_stratum=[self.stratum(line[0]) for line in lines]
            target_edge_index=[0 for line in lines]
            i=0
            while i<len(lines):
                line=lines[i]
                for j in xrange(1,len(line)):
                    sj=self.stratum(line[j])
                    if sj>highest_stratum[i]:
                        highest_stratum[i]=sj
                        highest_edges[i]=[j]
                    elif sj==highest_stratum[i]:
                        highest_edges[i].append(j)
                if len(highest_edges[i])==1 or not self.is_exponential_stratum(highest_stratum[i]): #It is safe to contract towards any edge in the upper most stratum
                    target_edge_index[i]=highest_edges[i][0]
                elif safe_strata and highest_stratum[i] in safe_strata: #It is safe to contract to any edge in the upper most stratum corresponding to the lowest coefficient of the right eigen-vector
                    M=self.relative_matrix(highest_stratum[i])
                    vectors=M.eigenvectors_right()
                    pf=0
                    pfv=[]
                    for (e,v,n) in vectors:
                        if e in AA and e>pf: 
                            pfv=v[0]
                            pf=e
                    least_index=highest_edges[i][0]
                    index=dict((a,k) for k,a in enumerate(self._strata[highest_stratum[i]]))
                    least_vector=pfv[index[self._domain._alphabet.to_positive_letter(line[highest_edges[i][0]])]]
                    for j in xrange(1,len(highest_edges[i])):
                        current_vector=pfv[index[self._domain._alphabet.to_positive_letter(line[highest_edges[i][j]])]]
                        if current_vector<least_vector:
                            least_index=highest_edges[i][j]
                            least_vector=current_vector
                    target_edge_index[i]=least_index
                else: #We need to cut the line in parts: one part for each edge of the uppermost stratum.
                    tmp_lines=[]
                    tmp_target_edge_index=[]
                    if highest_edges[i][1]>2:
                        tmp_lines.append(line[:highest_edges[i][1]])
                        tmp_target_edge_index.append(highest_edges[i][0])
                    for k in xrange(2,len(highest_edges[i])-1,2):
                        if highest_edges[i][k+1]-highest_edges[i][k-1]>2:
                            tmp_lines.append(line[highest_edges[i][k-1]+1:highest_edges[i][k+1]])
                            tmp_target_edge_index.append(highest_edges[i][k]-highest_edges[i][k-1]-1)
                    if len(highest_edges[i])%2==0 and len(line)-highest_edges[i][-2]>2:
                        tmp_lines.append(line[highest_edges[i][-2]+1:])
                        tmp_target_edge_index.append(highest_edges[i][-1]-highest_edges[i][-2]-1)
                    elif len(highest_edges[i])%2==1 and len(line)-highest_edges[i][-1]>1:
                        tmp_lines.append(line[highest_edges[i][-1]:])
                        tmp_target_edge_index.append(0)
                        
                    lines=lines[:i]+tmp_lines+lines[i+1:]
                    target_edge_index=target_edge_index[:i]+tmp_target_edge_index+target_edge_index[i+1:]
                    highest_edges=highest_edges[:i]+[[j] for j in tmp_target_edge_index]+highest_edges[i+1:]
                    highest_stratum=highest_stratum[i:]+[self.stratum(line[0]) for line in tmp_lines]+highest_stratum[i+1:]
                    i+=len(tmp_lines)-1

                i+=1

            if len(lines)>0:
                
                #Do not fusion a line if it breaks property RTT-i 
                i=0
                while i<len(lines):
                    line=lines[i] #TODO: only for highest stratum exponential ?
                    if highest_edges[i][0]>0:
                        left_line=line[:highest_edges[i][0]]
                        left_target=0
                        left_top_stratum=self.stratum(left_line[0])
                        for j in xrange(1,len(left_line)):
                            e=left_line[j]
                            s=self.stratum(e)
                            if s>left_top_stratum: 
                                left_top_stratum=s
                                left_target=j
                            
                        if not self.is_exponential_stratum(left_top_stratum): #we need to cut the left part
                            if len(left_line)>1:
                                lines.insert(i,left_line)
                                target_edge_index.insert(i,left_target)
                                highest_edges.insert(i,left_target)
                                i=i+1
                            lines[i]=line[highest_edges[i][0]:]
                            target_edge_index[i]-=highest_edges[i][0]
                            highest_edges[i]=[j-highest_edges[i][0] for j in highest_edges[i]]
                                                            
                    line=lines[i]           

                    if highest_edges[i][-1]<len(line)-1:
                        right_line=line[highest_edges[i][-1]+1:]
                        right_top_stratum=self.stratum(right_line[0])
                        right_target=0
                        for j in xrange(1,len(right_line)):
                            e=right_line[j]
                            s=self.stratum(e)
                            if s>right_top_stratum: 
                                right_top_stratum=s
                                right_target=j

                        if not self.is_exponential_stratum(right_top_stratum): #we need to cut the right part
                            if len(right_line)>1:
                                lines.insert(i,right_line)
                                target_edge_index.insert(i,right_target)
                                highest_edges.insert(i,right_target)
                                i=i+1
                            lines[i]=lines[i][:highest_edges[i][-1]+1]

                    if len(lines[i])<2:
                        lines.pop(i)
                        target_edge_index.pop(i)
                        highest_edges.pop(i)
                        i=i-1

                    i=i+1


                if len(lines)>0:
                    strata=self._strata
                    self._strata=False
                    tmp_morph=self.fusion_lines(lines,target_edge_index,verbose)

                    #If there was fusionned lines, contract pretrivial forest

                    pretrivial_forest=self.pretrivial_forest()
                    if len(pretrivial_forest)>0:
                        tmp_morph=self.contract_invariant_forest(pretrivial_forest,verbose)*tmp_morph
                    self._strata=strata
                    self.update_strata(tmp_morph,verbose)
                    if result_morph: 
                        result_morph=tmp_morph*result_morph
                    else:
                        result_morph=tmp_morph

        else:
            if verbose: print "No valence 2 vertices"
            
        if not result_morph:
            result_morph=WordMorphism(dict((a,Word([a])) for a in self._domain._alphabet))

        return result_morph



    def find_inessential_connecting_paths(self,s,verbose=False):
        """
        The list of inessential connecting path in the invariant
        subgraph below the ``s`` stratum. 

        INPUT:

        ``s``: the index of a stratum of ``self``

        OUPUT:

        A list of paths. Each path is given as a list of edges.
        """

        result=[]

        G=self._domain
        A=G.alphabet()

        #Build vertices between stratum s and strata below
        
        vertices_up=set(G.initial_vertex(a) for a in self._strata[s])
        vertices_up.update(G.terminal_vertex(a) for a in self._strata[s])

        edges_below=set(self._strata[0])
        for i in xrange(1,s):
            edges_below.update(self._strata[i])

        vertices_below=set(G.initial_vertex(a) for a in edges_below)
        vertices_below.update(G.terminal_vertex(a) for a in edges_below)

        vertices_border=vertices_below.intersection(vertices_up)

        if verbose: print "Border vertices: ",vertices_border

        #Build the lists of vertices in the border mapped to the same vertex

        preimage={}
        multiple_preimages={} #vertices of the border with at least two preimages by self
        done=True
        for v in vertices_border:
            vv=self(v)
            if vv in multiple_preimages:
                multiple_preimages[vv].append(v)
            elif vv in preimage:
                multiple_preimages[vv]=[preimage[vv],v]
                v0=vv
                done=False
            else:
                preimage[vv]=v

        if done: return []

        #Build a tree rooted at v0 that spans G and the list of remaining edges (loops)

        tree={v0:['',v0]}
        edges=A.positive_letters()
        loops=[]

        while len(edges)>0:
            new_edges=[]
            for a in edges:
                v=G.initial_vertex(a)
                vv=G.terminal_vertex(a)
                if v in tree and vv in tree:
                    loops.append(a)
                elif v in tree:
                    tree[vv]=[A.inverse_letter(a),v]
                elif vv in tree:
                    tree[v]=[a,vv]
                else:
                    new_edges.append(a)
            edges=new_edges
            
        if verbose: 
            print "Spanning tree: ",tree
            print "Remaining edges: ",loops

        #Build the list of paths to the root of the tree
        rootpath={}
        for v in tree:
            u=[]
            vv=v
            [a,vvv]=tree[vv]
            while vv!=v0: 
                u.append(a)
                vv=vvv
                [a,vvv]=tree[vv]
            rootpath[v]=Word(u)


        #Build the automorphism of the free group on loops defined by self
        B=AlphabetWithInverses(loops,[A.inverse_letter(a) for a in loops])
        FB=FreeGroup(B)
        
        phi_map={}
        for b in loops:
            wb=G.reverse_path(rootpath[G.initial_vertex(b)])*Word([b])*rootpath[G.terminal_vertex(b)]
            wwb=self(wb)
            
            phi_map[b]=FB(c for c in wwb if c in B)
        phi=FreeGroupAutomorphism(phi_map,FB)

        if verbose: print "Automorphism: ",phi

        #We need the inverse

        phi_inv=phi.inverse()


        #Build the list of paths from pairs of identified points of the border mapped to trivial paths 
        result=[]
        for v,vpreimages in multiple_preimages.iteritems():
            for i in xrange(len(vpreimages)-1):
                v1=vpreimages[i]
                for j in xrange(i+1,len(vpreimages)):
                    v2=vpreimages[j]
                    u1=rootpath[v1]
                    u2=rootpath[v2]
                    w=self(G.reverse_path(u1)*u2)
                    wB=FB(c for c in w if c in B)
                    wwB=phi_inv(wB)
                    ww=Word([])
                    for b in wwB:
                        ww=ww*G.reverse_path(rootpath[G.initial_vertex(b)])
                        ww=ww*Word([b])
                        ww=ww*rootpath[G.terminal_vertex(b)]
                    ww=u1*ww*G.reverse_path(u2)
                    ww=G.reduce_path(ww)
                    result.append(ww)

        #Removes from the result list the paths that are not below stratum s
        rresult=[]
        for i,w in enumerate(result):
            for b in w:
                b=A.to_positive_letter(b)
                if b not in edges_below: break
            else:
                rresult.append(w)

        if verbose: print "Inessential connecting paths below stratum ",s,": ",rresult


        return rresult

    def fold_paths(self,paths,verbose):
        """
        Recursively fold the ``paths`` of ``self``. 

        INPUT:

        ``paths``: a list of paths. Each path is a reduced path mapped
        by ``self`` to a path homotopic to a point.

        After folding the paths, contract the tails and pretrivial forest.

        WARNING:

        Does not do anything to the possible strata of self.

        """
        G=self._domain
        A=G.alphabet()
        result_morph=None

        for p in paths:
            if result_morph:
                p=G.reduce_path(result_morph(p))

            if verbose: print "Starting the fold of an inessential connecting path..."

            # We need to cleverly choose the place to fold.  The
            # strategy is to fold all possible places in p starting
            # with the oldest one. folds_order is the list of foldable
            # places in p in that order.

            i=0
            if len(p)>0:
                u=self.image(p[0])
            folds_order=[]
            while i+1<len(p):
                v=self.image(p[i+1])
                if len(u)==0 or len(v)==0:
                    folds_order.insert(0,i)
                elif A.are_inverse(u[-1],v[0]):
                    folds_order.append(i)
                i=i+1
                u=v
                    
            while len(p)>1: #because of previous foldings an edge can be contracted to a point
                if verbose: 
                    print "Fold path:",p,"order of folds to perform:",folds_order
                
                a=A.inverse_letter(p[folds_order[0]])
                b=p[folds_order[0]+1]
                u=self.image(a)
                v=self.image(b)
                cpl=G.common_prefix_length(u,v)
                common_prefix=u[:cpl]
                
                if cpl==len(u) and cpl==len(v):
                    folds_order[0]-=1
                else:
                    i=folds_order.pop(0)
                    if cpl==len(u) and i>0:
                        u=self.image(p[i-1])
                        if len(u)>0 and A.are_inverse(u[-1],v[cpl]): 
                            if A.are_inverse(p[i-1],p[i+1]):
                                folds_order.append(i-1)
                            else:
                                folds_order.insert(0,i-1)
                    elif cpl==len(v) and i+2<len(p):
                        v=self.image(p[i+2])
                        if len(v)>0 and u[cpl]==v[0]:
                            if A.are_inverse(p[i],p[i+2]):
                                folds_order.append(i)
                            else:
                                folds_order.insert(0,i)

                fold_morph=self.fold((a,b),common_prefix,verbose=verbose)

                q=G.reduce_path(fold_morph(p))
                for i in xrange(len(folds_order)):
                    u=G.reduce_path(fold_morph(p[:folds_order[i]+1]))
                    folds_order[i]=G.common_prefix_length(u,q)-1

                p=q
                
                if len(p)>1:
                    u=self.image(p[0])
                i=0
                folds=set()
                for i in xrange(len(p)-1):
                    v=self.image(p[i+1])
                    if len(u)==0 or len(v)==0 or A.are_inverse(u[-1],v[0]):
                        folds.add(i)
                    u=v

                new_folds_order=[]
                for i in folds_order:
                    if i in folds:
                        new_folds_order.append(i)
                        folds.remove(i)
                for i in folds:
                    new_folds_order.append(i)

                folds_order=new_folds_order

                if result_morph:
                    result_morph=fold_morph*result_morph
                else:
                    result_morph=fold_morph
    
        tails=self._domain.find_tails()
        if len(tails)>0:
            result_morph=self.contract_tails(tails,verbose)*result_morph
        forest=self.pretrivial_forest()
        if len(forest)>0:
            if result_morph:
                result_morph=self.contract_invariant_forest(forest,verbose)*result_morph
            else:
                result_morph=self.contract_invariant_forest(forest,verbose)
        return result_morph


    def relative_expansion_factors(self,verbose=False):
        """
        The expansion factors of the exponential strata of ``self``.

        It is assumed that all strata are irreducible.

        OUPUT:
        
        A dictionnary that maps the index of an exponential
        stratum to its expansion factor.

        """

        result={}
        for s in xrange(len(self._strata)):
            if self.is_exponential_stratum(s):
                
                eigenvalues=self.relative_matrix(s).eigenvalues()
                alpha=0
                for x in eigenvalues:
                    if x in AA and x>alpha: alpha=x
                result[s]=alpha
        return result
                

    def relative_train_track(self,verbose=False):
        """
        Gets a relative train-track map from ``self``. 

        ``self`` is assumed to be a non irreducible representative
        with at least two strata.

        ALGORITHM:

        1/ Completely reduce self.

        2/ For each exponential stratum from top to bottom: 

              2.1/ core subdivide the stratum

              2.2/ fold inessential connecting paths below the stratum
        
              2.3/ look for a multifold 

              2.4/ if any multifold:

                   2.4.1/ fold it

                   2.4.2/ reduces the stratum

                   2.4.3/ go back to 2/

        SEE ALSO:

        ``TopologicalRepresentative.stable_train_track()``.

        """

        A=self._domain.alphabet()

        result_morph=self.relative_reduce(safe_strata=range(len(self._strata)),verbose=verbose)

        done=False
        
        while not done:
            done=True

            if verbose:
                print "Expansion factors:",self.relative_expansion_factors()

            s=len(self._strata)-1
            while s>=0:
                if self.is_exponential_stratum(s):
                    need_reduction=False
                    if s>0:

                        #Core subdivision
                        l=len(self._strata)
                        result_morph=self.core_subdivide(s,verbose)*result_morph
                        number_of_new_strata=len(self._strata)-l #number of strata below s may have changed
                        s=s+number_of_new_strata
                        if number_of_new_strata>0: 
                            done=False #  Some core subdivision occured

                        #Inesssential connecting paths

                        paths=self.find_inessential_connecting_paths(s,verbose and (verbose-1))
                        if len(paths)>0:
                            if verbose:
                                print "Inessential connecting paths below stratum ",s,": ",paths
                            strata=self._strata
                            self._strata=False
                            tmp_morph=self.fold_paths(paths,verbose)
                            self._strata=strata
                            heritage=self.update_strata(tmp_morph,verbose)
                            s=heritage[s][0] #folding inessential connecting paths keeps the stratum irreducible and exponential

                            result_morph=tmp_morph*result_morph
                            done=False
                        elif verbose:
                            print "Stratum",s,"satisfies RTT-ii (no inessential connecting paths below)."

                    # Foldings

                    folded_strata=[]
                    turn=self.find_relative_folding(s,verbose)

                    if len(turn)>0:
                        strata=self._strata
                        self._strata=False
                        tmp_morph=self.multifold(turn,verbose)
                        
                        self._strata=strata
                        heritage=self.update_strata(tmp_morph,verbose)
                        folded_strata=heritage[s] 
                        s=heritage[s][0]
                        
                        result_morph=tmp_morph*result_morph

                        result_morph=self.relative_reduce(folded_strata,verbose)*result_morph
                        done=False
                        break

                    elif verbose:
                        print "Stratum",s,"satisfies RTT-iii (no illegal turns in the image of edges)."
                

                s=s-1



        return result_morph

    def inessential_inp(self,inps,s,verbose):
        """
        From the list ``inps`` returns either an inessential inp in the
        stratum ``s`` or ``False``.

        INPUT:

        - ``inps`` : a list of inps each of the form ``(word1,word2)``.

        - ``s`` : the index of the exponential stratum of ``self``
          that meets these inps.

        """

        A=self._domain.alphabet()

        M=self.relative_matrix(s)
        vectors=M.eigenvectors_left()
        pf=0
        for (e,v,n) in vectors:
            if e in AA and e>pf: 
                pfv=v[0]
                pf=e      

        critic=0 #the length of the common prefix of an issential inp
        i=0
        pfvl=dict()
        for a in self._strata[s]:
            critic+=pfv[i]
            pfvl[a]=pfv[i]
            i+=1

        critic=critic*(pf-1)

        for inp in inps:
            prefix=self(inp[0])[:self._domain.common_prefix_length(self(inp[0]),self(inp[1]))]                

            prefix_length=0  
            for a in prefix:
                aa=A.to_positive_letter(a)
                if aa in self._strata[s]:
                    prefix_length+=pfvl[aa] 
            if prefix_length!=critic:
                return inp
        return None


    def stable_relative_train_track(self,verbose=False):
        """
        Gets a stable relative train-track map from ``self``. 

        ``self`` is assumed to be a non irreducible topological
        representative with at least two strata.

        ALGORITHM:

        1/ Completely reduce self.

        2/ For each exponential stratum s from top to bottom: 

             a/ core subdivide s

             b/ look for inessential connecting paths below s and fold
             them.

             c/find a multifold in s and fold if any.

             d/ If some fold occured at step c/ reduces self and come back to a/

             e/ look for indivisible paths that intersect the interior
             of s. If there are fold until a partial fold occurs and
             then come back to a/.

        OUPUT:

        A WordMorphism that maps old edges to paths in the new graph.

        """

        G=self._domain
        A=G.alphabet()

        result_morph=self.relative_reduce(safe_strata=range(len(self._strata)),verbose=verbose)

        s=len(self._strata)-1
        while s>=0:

            done=False
            while not done: #at the end stratum s satisfies RTT and is stable
                done=True

                if self.is_exponential_stratum(s):
                    if s>0:
                        
                        if verbose:
                            print "Exponential stratum",s,"expansion factor",self.expansion_factor(s)

                        #Core subdivision
                        l=len(self._strata)
                        result_morph=self.core_subdivide(s,verbose)*result_morph
                        number_of_new_strata=len(self._strata)-l #number of strata below s may have changed
                        s=s+number_of_new_strata

                        #Inesssential connecting paths

                        paths=self.find_inessential_connecting_paths(s,verbose and (verbose-1))
                        if len(paths)>0:
                            if verbose:
                                print "Inessential connecting paths below stratum ",s,": ",paths
                            strata=self._strata
                            self._strata=False
                            tmp_morph=self.fold_paths(paths,verbose)
                            self._strata=strata
                            heritage=self.update_strata(tmp_morph,verbose)
                            s=heritage[s][-1] #folding inessential connecting paths keeps the stratum irreducible and exponential

                            result_morph=tmp_morph*result_morph
                        elif verbose:
                            print "Stratum",s,"satisfies RTT-ii (no inessential connecting paths below)."

                    # Foldings

                    turn=self.find_relative_folding(s,verbose)
                    if len(turn)>0:
                        done=False

                        strata=self._strata
                        self._strata=False
                        tmp_morph=self.multifold(turn,verbose)                        
                        self._strata=strata
                        heritage=self.update_strata(tmp_morph,verbose)

                        folded_strata=heritage[s] 
                        s=heritage[s][-1]

                        result_morph=tmp_morph*result_morph

                        stratum=set(a for a in self._strata[s])
                        tmp_morph=self.relative_reduce(folded_strata,verbose)
                        result_morph=tmp_morph*result_morph

                        new_s=0 # we now consider the highest stratum that inherits from s
                        for a in stratum:
                            for b in tmp_morph.image(a):
                                sb=self.stratum(b)
                                if sb>new_s:
                                    new_s=sb
                        s=new_s


                    else:  # now stratum s satisfies RTT
                        if verbose:
                            print "Stratum",s,"satisfies RTT-iii (no illegal turns in the image of edges)."

                        inps=self.relative_indivisible_nielsen_paths(s,verbose and (verbose-1))
                        if len(inps)==0:
                           if verbose: 
                               print "No INP in stratum",s
                        else:
                            
                            inp_done=False
                            while not inp_done:
                                inp_done=True
                                if verbose:
                                    print "INPs in stratum",s,":",inps
                                inp=self.inessential_inp(inps,s,verbose and (verbose-1))
                                if inp:
                                    done=False
                                    if verbose:
                                        print "Inessential INP:",inp
                                    folding_morph=self.fold_inp_in_relative_train_track(inp,s,verbose)
                                    result_morph=folding_morph*result_morph

                                    heritage=self.update_strata(folding_morph,verbose)
                                    s=heritage[s][-1]
                                else:
                                    edges=[a for a in self._strata[s]]
                                    edges=edges+[A.inverse_letter(a) for a in edges]
                                    turns=[]
                                    for i in xrange(len(edges)-1):
                                        for j in xrange(i+1,len(edges)):
                                            a=edges[i]
                                            b=edges[j]
                                            if G.initial_vertex(a)==G.initial_vertex(b):
                                                if A.less_letter(a,b):
                                                    turns.append((a,b))
                                                else:
                                                    turns.append((b,a))

                                    for turn in turns:
                                        tt=self.image_turn(turn)
                                        if tt[0]==tt[1] and any((turn[0]!=inp[0][0] or turn[1]!=inp[1][0]) for inp in inps):
                                            done=False
                                            inp_done=False
                                            if verbose: print "Fold illegal turn: ",turn
                                            u=self.image(turn[0])
                                            prefix=u[0:G.common_prefix_length(u,self.image(turn[1]))]
                                            folding_morph=self.fold(turn,prefix,verbose)
                                            
                                            heritage=self.update_strata(folding_morph,verbose)
                                            s=heritage[s][-1]
                                            inps=[(folding_morph(t[0]),folding_morph(t[1])) for t in inps]
                                            for i in xrange(len(inps)):
                                                inp=inps[i]
                                                cpl=G.common_prefix_length(inp[0],inp[1])
                                                if cpl>0:
                                                    inps[i]=(inp[0][cpl:],inp[1][cpl:])
                                            result_morph=folding_morph*result_morph
                                            break
                                            
                                    else:
                                        for turn in turns:
                                            tt=self.image_turn(turn)
                                            if any((tt[0]==inp[0][0] and tt[1]==inp[1][0]) for inp in inps):
                                                done=False
                                                inp_done=False
                                                if verbose: print "Fold illegal turn :",tt
                                                u=self.image(tt[0])
                                                prefix=u[0:G.common_prefix_length(u,self.image(tt[1]))]
                                                folding_morph=self.fold(tt,prefix,verbose)

                                                heritage=self.update_strata(folding_morph,verbose)
                                                s=heritage[s][-1]
                                                inps=[(folding_morph(t[0]),folding_morph(t[1])) for t in inps]
                                                for i in xrange(len(inps)):
                                                    inp=inps[i]
                                                    cpl=G.common_prefix_length(inp[0],inp[1])
                                                    if cpl>0:
                                                        inps[i]=(inp[0][cpl:],inp[1][cpl:])

                                                result_morph=folding_morph*result_morph
                                                break
                                        
                                            

            s=s-1



        return result_morph
