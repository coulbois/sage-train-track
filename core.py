#*****************************************************************************
#
#
# modified by Thierry
#
#*****************************************************************************

# from free_group import FreeGroup
# from inverse_graph import GraphWithInverses
    
class Core():
    """
    Core(G,H,g,h,v,w) builds the Guirardel Core for the two GraphWithInverse
    objects G and H where g: G -> H and h: H -> G are homotopy inverses and
    v and w are the corresponding (optional) vertex maps.

    Core(G,H) builds the Guirardel Core for the two MarkedGraph
    objects G and H.

    AUTHORS:

    - Matt Clay

    """

    def __init__(self,domain,codomain,edge_map=None,inv_edge_map=None,vertex_map=None,\
                 inv_vertex_map=None,consolidate=False):

        self._domain=domain
        self._codomain=codomain
        if edge_map is None:
            edge_map=domain.difference_of_marking(codomain).tighten().edge_map()
        if inv_edge_map is None:
            inv_edge_map=codomain.difference_of_marking(domain).edge_map()
        self._graph_map=GraphMap(domain,codomain,edge_map,vertex_map)
        self._inv_graph_map=GraphMap(codomain,domain,inv_edge_map,inv_vertex_map)
        
        self._signed_ends={} # dictionary: keys = edge labels and inverse labels of domain
                             # signed_ends[x] = +- cylinder decomoposition of image of edge_map
        self._core_slice={} # dictionary: keys = edge labels of domain
                            # core_slice[x] = slice of the core above x as a GraphWithInverses

        self._build_endmap(consolidate)
        self._build_core()

    def __str__(self):
        """
        String representation.
        """
        result="Core of:\n"
        result=result+str(self._graph_map)+"\n"
        result=result+str(self._inv_graph_map)+"\n"
        result=result+"Map on ends:\n"
        for x in self._signed_ends.keys():
            result=result+str(x)+": "+str(self._signed_ends[x])+"\n"
        result=result+"Slices of core:\n"
        #for x in self._core_slice.keys(): # doesn't work right as some letters in the alphabet are not used to label edges
        #    result=result+str(x)+": "+str(self._core_slice[x])+"\n"
        result=result+"Volume: "+str(self.volume())
        return result

    def _build_endmap(self,consolidate=False):
        """
        Builds the map on ends for graph_map.  Called when Core is initialized.
        """
        alph=self._graph_map.domain()._alphabet
        inv_alph=self._inv_graph_map.domain()._alphabet
        FA=FreeGroup(alph)
        FB=FreeGroup(inv_alph)
        for x in self._graph_map.domain().edge_labels():
            X=alph.inverse_letter(x)
            self._signed_ends[x]=[]
            self._signed_ends[X]=[]
        
        for x in self._inv_graph_map.domain().edge_labels():
            X=inv_alph.inverse_letter(x)
            inv_image_x = self._inv_graph_map(x)
            vp='' # vanishing path
            for a in inv_image_x:
                A=alph.inverse_letter(a)
                if vp=='' or vp[-1]!=X: # coming from + side, no cancellation
                    self._signed_ends[a].append(vp + x)
                else: # coming from - side, cancels x
                    self._signed_ends[a].append('-' + vp) # - + vp #
                # add to vanishing path
                vp=str(FB.reduced_product(str(self._graph_map(A)),vp))
                # repeat for inverse, we've added to the vanishing path because we are
	  	# coming from the other side
                if vp=='' or vp[-1]!=X: # coming from - side, no cancellation
                    self._signed_ends[A].append('-' + vp + x) # - + vp + x
                else: # coming from + side, cancels x
                    self._signed_ends[A].append(vp)

        if consolidate:
            for a in self._signed_ends.keys():
                removed_end=True
                N=2*inv_alph.cardinality() # should take into account the actual vertex...
                while removed_end:
                    removed_end=False
                    prefix=[]
                    for e in self._signed_ends[a]:
                        prefix.append(e[:-1])
                    prefix_counts=dict((p,prefix.count(p)) for p in set(prefix))
                    for p in prefix_counts.keys():
                        p_opp = p[1:] if p[:1]=='-' else '-'+p
                        removed_ends=[]
                        tails=[]
                        if prefix_counts[p]==N-1:
                            removed_end=True
                            for e in self._signed_ends[a]:
                                if e[:-1]==p:
                                    removed_ends.append(e)
                                    tails.append(e[-1:])
                            if p=='' or p=='-':
                                for aa in inv_alph:
                                    if aa not in tails: self._signed_ends[a].append(p_opp+aa)
                            else: self._signed_ends[a].append(p)
                            for e in removed_ends: self._signed_ends[a].remove(e)
                        if prefix_counts[p]==N-2 and p_opp in self._signed_ends[a]:
                            removed_end=True
                            for e in self._signed_ends[a]:
                                if e[:-1]==p:
                                    removed_ends.append(e)
                                    tails.append(e[-1:])
                            tails.append(inv_alph.inverse_letter(p[-1:]))
                            for aa in inv_alph:
                                if aa not in tails: self._signed_ends[a].append(p_opp+aa)
                            for e in removed_ends: self._signed_ends[a].remove(e)
                            self._signed_ends[a].remove(p_opp)   
                            
    def _build_core(self):
        """
        Builds the core.  Called when Core is initialized.
        """
        ends={} # remove signs from ends
        for x in self._signed_ends.keys():
            ends[x]=[]
            for e in self._signed_ends[x]:
                ends[x].append(e[1:] if e[0]=='-' else e)
        inv_alph=self._inv_graph_map.domain()._alphabet
        
        for x in self._graph_map.domain().edge_labels():
            slice_x=GraphWithInverses(alphabet=inv_alph)
            # find common prefix
            if ends[x]: common=ends[x][0]
            for e in ends[x]:
                common_len=self._inv_graph_map.domain().common_prefix_length(e,common)
                common=common[:common_len]
            # build slice
            for e in ends[x]:
                v_label=common
                for a in e[common_len:-1]:
                    if v_label not in slice_x.vertices():
                        slice_x.add_vertex(v_label)
                    t_label=v_label+a
                    if t_label not in slice_x.vertices():
                        slice_x.add_vertex(t_label)
                    edge=(v_label,t_label,a)
                    if edge not in slice_x.edges():
                        slice_x.add_edge(edge)
                    v_label=t_label
            self._core_slice[x]=slice_x


    def end_map(self,e=None):
        """
        Returns the image as a union (+) and difference (-) of cylinders of the
        one-sided cylinder determined by e if specified.  Else returns the dictionary
        defined by the map on ends.
        """
        if e==None or e not in self._signed_ends.keys():
            return self._signed_ends
        else:
            return self._signed_ends[e]
  
    def core_slice(self,e=None):
        """
        The slice of core above e if specified.  Else returns the dictionary
        of core slices.
        """
        if e==None or e not in self._core_slice.keys():
            return self._core_slice
        else:
            return self._core_slice[e]

        

    def volume(self,e=None):
        """
        Returns the volume the slice of core above e if
        specified. Else returns the volume of the core, i.e., the
        intersection number.
        """
        if e==None or e not in self._core_slice.keys():
            return sum(len(self._core_slice[x].edges()) for x in self._core_slice.keys()) # intersection number
        else:
            return len(self._core_slice[e].edges())

    @staticmethod
    def rose_map(automorphism):
        """
        Returns the core of the rose and the rose acted upon by the corresponding
        automorphism.
        """

        graph=GraphWithInverses.rose_graph(automorphism._domain._alphabet.copy())
        inv_automorphism=automorphism.inverse()
        return Core(graph,graph,automorphism,inv_automorphism)
    
