#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from sage.graphs.graph import DiGraph
from sage.combinat.words.word import Word


class GraphWithInverses(DiGraph):
     """
     A GraphWithInverses is a simplicial oriented graph, with labeled
     edges. Labels form an AlphabetWithInverses.  Each edge has a
     reversed edge. This is intended to be consistent with Serre's
     definition of graph in [Trees].

     ``GraphWithInverses`` can be created from:

     - a dictionnary that maps letters of the alphabet to lists
     ``(initial_vertex,terminal_vertex)``

     or alternatively

     - from a list of edges: ``[initial_vertex,terminal_vertex,letter]``.

     EXAMPLES::

     sage: print GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
     Graph with inverses: a: 0->0, b: 0->1, c: 1->0

     sage: print GraphWithInverses([[0,0,'a'],[0,1,'b'],[1,0,'c']])
     Graph with inverses: a: 0->0, b: 0->1, c: 1->0

     AUTHORS:

     - Thierry Coulbois (2013-05-16): beta.0 version
     """
     def __init__(self,data=None,alphabet=None):

          self._initial={}
          self._terminal={}

          letters=[]
          if isinstance(data,dict):
               new_data=dict()
               for a in data:
                    letters.append(a)
                    if data[a][0] in new_data:
                         if data[a][1] in new_data[data[a][0]]:
                              new_data[data[a][0]][data[a][1]].append(a)
                         else:
                              new_data[data[a][0]][data[a][1]]=[a]
                    else:
                         new_data[data[a][0]]={data[a][1]:[a]}

               data=new_data

          elif isinstance(data,list):
               new_data=dict()
               for e in data:
                    letters.append(e[2])
                    if e[0] in new_data:
                         if e[1] in new_data[e[0]]:
                              new_data[e[0]][e[1]].append(e[2])
                         else:
                              new_data[e[0]][e[1]]=[e[2]]
                    else:
                         new_data[e[0]]={e[1]:[e[2]]}
               data=new_data


          if alphabet is None:
              from inverse_alphabet import AlphabetWithInverses
              alphabet = AlphabetWithInverses(self._initial.keys())

          self._alphabet=alphabet


          DiGraph.__init__(self,data=data,loops=True,multiedges=True,vertex_labels=True,pos=None,format=None,\
                                boundary=[],weighted=None,implementation='c_graph',sparse=True)


          for e in self.edges():
               self._initial[e[2]]=e[0]
               self._terminal[e[2]]=e[1]
               self._initial[alphabet.inverse_letter(e[2])]=e[1]
               self._terminal[alphabet.inverse_letter(e[2])]=e[0]



     def copy(self):
          """
          A copy of ``self``.

          WARNING:

          The alphabet is NOT copied.
          """

          return self.__class__(self,alphabet=self._alphabet)


     def __str__(self):
          """
          String representation of ``self``.
          """
          result="Graph with inverses: "
          for a in self._alphabet.positive_letters():
               result=result+a+": {0}->{1}, ".format(self.initial_vertex(a),self.terminal_vertex(a))
          result=result[:-2]
          return result

     def alphabet(self):
          """
          The ``AlphabetWithInverses`` that labels the edges of ``self``.
          """
          return self._alphabet

     def initial_vertex(self,edge_label):
          """
          Initial vertex of the edge labeled with ``edge_label`.
          """
          return self._initial[edge_label]

     def set_initial_vertex(self,e,v):
          """
          Sets the initial vertex of the edge ```e`` to the vertex
          ``v``.

          Consistantly sets the terminal vertex of the edge label by
          the inverse of ``e`` to the vertex ``v``.
          """

          w=self.initial_vertex(e)
          ww=self.terminal_vertex(e)
          pe=self._alphabet.to_positive_letter(e)
          if e==pe:
               DiGraph.delete_edge(self,w,ww,pe)
               DiGraph.add_edge(self,v,ww,pe)
          else:
               DiGraph.delete_edge(self,ww,w,pe)
               DiGraph.add_edge(self,ww,v,pe)
          self._initial[e]=v
          self._terminal[self._alphabet.inverse_letter(e)]=v


     def terminal_vertex(self,edge_label):
          """
          Terminal vertex of the edge labeled by ``edge_label``.
          """

          return self._terminal[edge_label]

     def set_terminal_vertex(self,e,v):
          """
          Sets the terminal vertex of the edge ``e`` to the vertex
          ``v``.

          Consistantly sets the initial vertex of the edge label by
          the inverse of ``e`` to the vertex ``v``.
          """
          w=self.initial_vertex(e)
          ww=self.terminal_vertex(e)
          pe=self._alphabet.to_positive_letter(e)
          if e==pe:
               DiGraph.delete_edge(self,w,ww,pe)
               DiGraph.add_edge(self,w,v,pe)
          else:
               DiGraph.delete_edge(self,ww,w,pe)
               DiGraph.add_edge(self,v,w,pe)

          self._terminal[e]=v
          self._initial[self._alphabet.inverse_letter(e)]=v

     def reverse_path(self,path):
          """
          Reverse path of ``path``.
          """
          return Word([self._alphabet.inverse_letter(e) for e in reversed(path)])

     def add_edge(self,u,v=None,label=None):
          """
          Add a new edge.

          INPUT: The following forms are all accepted

          - G.add_edge(1,2,'a')
          - G.add_edge((1,2,'a'))
          - G.add_edge(1,2,['a','A'])
          - G.add_edge((1,2,['a','A']))

          OUTPUT:

          the label of the new edge.

          WARNING:

          Does not change the alphabet of ``self``. (the new label is
          assumed to be already in the alphabet).

          """

          if label is None:
               v=u[1]
               label=u[2]
               u=u[0]

          if isinstance(label,list):
               DiGraph.add_edge(self,u,v,label[0])
               self._initial[label[0]]=u
               self._initial[label[1]]=v
               self._terminal[label[1]]=u
               self._terminal[label[0]]=v
               label=label[0]

          else:
               DiGraph.add_edge(self,u,v,label)
               self._initial[label]=u
               self._terminal[label]=v
               inv_label=self.alphabet().inverse_letter(label)
               self._initial[inv_label]=v
               self._terminal[inv_label]=u

          return label

     def new_vertex(self):
          """
          The least integer that is not a vertex of ``self``.
          """
          i=0
          done=False
          while not done:
               if i not in self.vertices():
                   done=True
               i=i+1
          return i-1

     def new_vertices(self,n):
          """
          A list of length ``n`` of integers that are not vertices of
          ``self``.
          """
          i=0
          result=[]
          while n>0:
               if i not in self.vertices():
                   result.append(i)
                   n=n-1
               i=i+1
          return result


     def add_vertex(self,i=None):
          """
          Add a new vertex with label ``i`` or the least integer which
          is not already a vertex.

          OUTPUT:

          the new vertex.
          """
          if i==None:
               i=self.new_vertex()
          DiGraph.add_vertex(self,i)
          return i

     def remove_edge(self,e):
          """
          Removes the edge ``e`` (together with its inverse). Removes ``e``
          (and its inverse) from the alphabet.
          """
          pe=self._alphabet.to_positive_letter(e)
          ee=self._alphabet.inverse_letter(e)
          DiGraph.delete_edge(self,self.initial_vertex(pe),self.terminal_vertex(pe),pe)
          self._alphabet.remove_letter(e)
          self._initial.pop(e)
          self._initial.pop(ee)
          self._terminal.pop(e)
          self._terminal.pop(ee)

     def remove_vertex(self,v):
          """
          Removes the vertex ``v`` from ``self``.

          WARNING:

          ``v`` must be an isolated vertex.

          """
          DiGraph.delete_vertex(self,v)

     def reduce_path(self,path):
          """
          Reduced path homotopic (relative to endpoints) to ``path``.
          """
          result = list(path)

          i=0
          j=1
          long=len(result)
          while (j<long):
               k=0
               while i-k>=0 and j+k<long and self._alphabet.are_inverse(result[i-k],result[j+k]): k=k+1
               i=i-k+1
               j=j+k+1
               if j-1<long:
                    result[i]=result[j-1]
               else:
                    i=i-1
          return Word(result[0:i+1])

     def common_prefix_length(self,p,q):
        """
        Length of the common prefix of the paths ``p`` and ``q``.

        WARNING:

        ``p`` and ``q`` are assumed to be reduced.

        EXAMPLES::

        sage: rose_graph(AlphabetWithInverses(3)).common_prefix_length("aBaa","aBcb")
        2
        """
        k=0
        while(k<len(p) and k<len(q) and p[k]==q[k]): k=k+1
        return k

     def is_prefix(self,p,q):
          """
          ``True`` if the path ``p`` is a prefix of ``q``.

          WARNING:

          ``p`` and ``q`` are assumed to be reduced.

          """

          i=0
          l=len(p)
          if l<=len(q):
               done=False
               while i<l and not done:
                    done= not p[i]==q[i]
                    i=i+1
               return not done
          else:
               return False



     def connected_components(self,edge_list=None):
          """
          The list of connected components (each as a list of
          edges) of the subgraph of ``self`` spanned by ``edge_list``.
          """
          if edge_list==None: return DiGraph.connected_components(self)
          components=[]
          vertices=[]
          for e in edge_list:
               v=self.initial_vertex(e)
               vv=self.terminal_vertex(e)
               t=[i for i in xrange(len(components)) if v in vertices[i] or vv in vertices[i]]
               if len(t)==0:
                    components.append([e])
                    if v!=vv:
                         vertices.append([v,vv])
                    else:
                         vertices.append([v])
               elif len(t)==1:
                    components[t[0]].append(e)
                    if v not in vertices[t[0]]:
                         vertices[t[0]].append(v)
                    elif vv not in vertices[t[0]]:
                         vertices[t[0]].append(vv)
               elif len(t)==2:
                    components[t[0]]=components[t[0]]+components[t[1]]+[e]
                    vertices[t[0]]=vertices[t[0]]+vertices[t[1]]
                    components.pop(t[1])
                    vertices.pop(t[1])
          return components


     def core_subgraph(self,edge_list):
          """
          Core subgraph (the list of edges that belong to at least one
          loop) of the subgraph of ``self`` spanned by edge_list.
          """

          A=self._alphabet
          core=[]
          tree=[]
          outgoing={}
          for e in edge_list:
               v=self.initial_vertex(e)
               vv=self.terminal_vertex(e)
               if v in outgoing.keys():
                    outgoing[v].append(e)
               else:
                    outgoing[v]=[e]
               if vv in outgoing.keys():
                    outgoing[vv].append(A.inverse_letter(e))
               else:
                    outgoing[vv]=[A.inverse_letter(e)]
          done=False
          while not done:
               done=True
               for v in outgoing.keys():
                    if len(outgoing[v])==1:
                         done=False
                         e=outgoing[v][0]
                         vv=self.terminal_vertex(e)
                         outgoing[v].remove(e)
                         outgoing[vv].remove(A.inverse_letter(e))
          for v in outgoing.keys():
               for e in outgoing[v]:
                    if A.is_positive_letter(e): core.append(e)
          return core



     def turns(self):
        """
        List of turns of the graph.

        A turn is a tuple (a,b) of edges outgoing from the same
        vertex. a is less than b in the ``self.alphabet()`` order.
        """
        A=self._alphabet
        return [(a,b) for a in A for b in A if a!=b and A.less_letter(a,b) and self.initial_vertex(a)==self.initial_vertex(b)]


     def extensions(self,u,turns):
          """
          List of edges a such that the turn between ``u`` and a is in ``turns``.
          """
          uu=self._alphabet.inverse_letter(u[-1])
          result=[]
          for t in turns:
               if t[0]==uu: result.append(t[1])
               elif t[1]==uu: result.append(t[0])
          return result



     def subdivide(self,edge_list):
          """
          Subdvides the edges in ``edge_list`` into two edges.

          WARNING:

          Edges in ``edge_list`` are assumed to be distinct.

          OUTPUT:

          A dictionnary that maps an old edge to a path in the new
          graph.
          """
          A=self._alphabet
          result_map=dict((e,Word([e])) for e in A)
          new_edges=A.add_new_letters(len(edge_list))
          new_vertices=self.new_vertices(len(edge_list))

          for i,e in enumerate(edge_list):
               ee=A.inverse_letter(e)
               v=new_vertices[i]
               vi=self.initial_vertex(e)
               vt=self.terminal_vertex(e)
               f=new_edges[i][0]
               ee=A.inverse_letter(e)
               ff=new_edges[i][1]
               self.set_terminal_vertex(e,v)
               self.add_edge(v,vt,[f,ff])
               result_map[e]=result_map[e]*Word([f])
               result_map[ee]=Word([ff])*result_map[ee]
          return result_map


     def fold(self,edges_full,edges_partial):
          """
          Folds the list of edges.

          Some edges are fully folded and some are only partially
          folded. All edges are assumed to start form the same vertex.
          Edges are given by their label.

          The first element of ``edges_full`` is allowed to be a tuple ``(path,'path')`` and
          not an ``edge_label``.

          OUTPUT:

          A dictionnay that maps an old edge to the path in
          the new graph.
          """

          A=self._alphabet
          edge_map=dict((e,Word([e])) for e in A)

          if len(edges_full)>0: # we just need to collapse edges
               e0=edges_full[0]
               if isinstance(e0,tuple) and e0[1]=='path': #e0 stands for a path
                    e0=e0[0]
               else:
                    e0=Word([e0])
               ee0=self.reverse_path(e0)
               v0=self.terminal_vertex(e0[-1])
               identified_vertices=set([v0])
               for e in edges_full[1:]:
                    identified_vertices.add(self.terminal_vertex(e))
                    edge_map[e]=e0
                    edge_map[A.inverse_letter(e)]=ee0
                    self.remove_edge(e)
          else:
               [e0,ee0]=A.add_new_letter()
               v0=self.new_vertex()
               self.add_edge(self.initial_vertex(edges_partial[0]),v0,[e0,ee0])
               e0=Word([e0])
               ee0=Word([ee0])

          for e in edges_partial:
               ee=A.inverse_letter(e)
               self.set_initial_vertex(e,v0)
               edge_map[e]=e0*edge_map[e]
               edge_map[ee]=edge_map[ee]*ee0

          if len(edges_full)>0:
               for e in A:
                    v=self.initial_vertex(e)
                    if v!=v0 and v in identified_vertices:
                         self.set_initial_vertex(e,v0)
               for v in identified_vertices:
                    if v!=v0:
                         self.remove_vertex(v)

          return edge_map



     def contract_edges(self,edge_list):
          """
          Contract a list of edges.

          Each connected component is contracted to one of its
          vertices.

          OUTPUT:

          A dictionnary that maps an old edge to its image in the new
          graph.
          """
          components=self.connected_components(edge_list)
          return self.contract_forest(components)


     def contract_forest(self,forest):
          """
          Contract the forest.

          Each tree of the forest is contracted to the initial vertex of its first
          edge.

          INPUT:

          ``forest`` is a list of disjoint subtrees each given as
          lists of edges.

          OUTPUT:

          A dictionnary that maps an old edge to its image in the new
          graph.
          """
          A=self._alphabet


          edge_map=dict((e,Word([e])) for e in A)
          vertex_map={}

          for tree in forest:
               first=True
               for e in tree:
                    if first:
                         vtree=self.initial_vertex(e)
                         first=False
                    vertex_map[self.initial_vertex(e)]=vtree
                    vertex_map[self.terminal_vertex(e)]=vtree
                    edge_map[e]=Word([])
                    edge_map[A.inverse_letter(e)]=Word([])
                    self.remove_edge(e)

          for e in A:
               v=self.initial_vertex(e)
               if v in vertex_map and v!=vertex_map[v]:
                    self.set_initial_vertex(e,vertex_map[self.initial_vertex(e)])
                    if self.has_vertex(v):
                         self.remove_vertex(v)

          return edge_map

     def find_tails(self):
          """
          The forest (as a list of list of edges) outside the core graph.

          (that is to say edges that do not belong to any loop in the
          graph.)
          """
          outgoing={}
          outgoing.update((v,[]) for v in self.vertices())
          A=self._alphabet
          for a in A.positive_letters():
               outgoing[self.initial_vertex(a)].append(a)
               outgoing[self.terminal_vertex(a)].append(A.inverse_letter(a))

          valence_1=[]
          edges_1=[]
          done=False
          while not done:
               done=True
               for v in self.vertices():
                    if len(outgoing[v])==1:
                         done=False
                         valence_1.append(v)
                         e=outgoing[v][0]
                         vv=self.terminal_vertex(e)
                         outgoing[vv].remove(A.inverse_letter(e))
                         outgoing[v].remove(e)
                         edges_1.append(e)
          forest=[]
          for e in reversed(edges_1):
              if self.terminal_vertex(e) in valence_1:
                   forest[len(forest)-1].append(A.inverse_letter(e))
              else:
                   forest.append([A.inverse_letter(e)])
          return forest


     def find_valence_2_vertices(self):
          """
          The list of paths with all inner vertices of valence 2.
          """
          outgoing={}
          outgoing.update((v,[]) for v in self.vertices())
          A=self._alphabet
          for a in A:
               outgoing[self.initial_vertex(a)].append(a)
          valence_2=set(v for v in outgoing if len(outgoing[v])==2)

          lines=[]

          while len(valence_2)>0:
               vi=valence_2.pop()
               vt=vi
               e=outgoing[vi][0]
               f=outgoing[vt][1]
               ee=A.inverse_letter(e)
               ff=A.inverse_letter(f)
               line=[ee,f]
               vi=self.terminal_vertex(e)
               vt=self.terminal_vertex(f)
               while vi in valence_2:
                    valence_2.remove(vi)
                    if outgoing[vi][0]==ee:
                         e=outgoing[vi][1]
                    else:
                         e=outgoing[vi][0]
                    ee=A.inverse_letter(e)
                    vi=self.terminal_vertex(e)
                    line.insert(0,ee)
               while vt in valence_2:
                    valence_2.remove(vt)
                    if outgoing[vt][0]==ff:
                         f=outgoing[vt][1]
                    else:
                         f=outgoing[vt][0]
                    ff=A.inverse_letter(f)
                    vt=self.terminal_vertex(f)
                    line.append(f)
               lines.append(line)


          return lines

     def maximal_tree(self):
          """
          A maximal tree for ``self``.

          OUTPUT:

          - A list of positive letters.

          WARNING:

          If ``self`` is not connected, returns a maximal tree of the
          connected component of the first edge labeled by the first
          letter of the alphabet.

          SEE ALSO:

          GraphWithInverses.spanning_tree()
          """

          tree=[]
          A=self._alphabet
          tree_vertices=[self.initial_vertex(A[0])]
          done=False
          while not done:
               done=True
               for a in A.positive_letters():
                    if self.initial_vertex(a) in tree_vertices and self.terminal_vertex(a) not in tree_vertices:
                         tree.append(a)
                         tree_vertices.append(self.terminal_vertex(a))
                         done=False
                    elif self.terminal_vertex(a) in tree_vertices and self.initial_vertex(a) not in tree_vertices:
                         tree.append(a)
                         tree_vertices.append(self.initial_vertex(a))
                         done=False
          return tree

     def spanning_tree(self):
          """
          A spanning tree.

          OUPUT:

          a dictionnary that maps each vertex to an edge-path from the origin vertex.

          SEE ALSO:

          ``maximal_tree()`` that returns a list of edges of a spanning tree.

          WARNING:

          ``self`` must be connected.
          """

          A=self._alphabet
          tree={self.initial_vertex(A[0]):Word()}

          done=False
          while not done:
               done=True
               for a in A.positive_letters():
                    vi=self.initial_vertex(a)
                    vt=self.terminal_vertex(a)
                    if vi in tree and vt not in tree:
                         tree[vt]=self.reduce_path(tree[vi]*Word([a]))
                         done=False
                    elif vt in tree and vi not in tree:
                         tree[vi]=self.reduce_path(tree[vt]*Word([A.inverse_letter(a)]))
                         done=False
          return tree



     def plot(self,edge_labels=True,graph_border=True,**kwds):
          return sage.graphs.graph.DiGraph.plot(sage.graphs.graph.DiGraph(self),edge_labels=edge_labels,graph_border=graph_border,**kwds)

     @staticmethod
     def valence_3(rank):
          """
          A strongly connected graph with all vertices of valence 3 and of given rank.

          ``rank`` is assumed to be greater or equal than 2.
          """

          graph=dict()
          A=AlphabetWithInverses(3*rank-3)
          for i in xrange(rank-2):
               graph[A[2*i]]=(2*i+1,2*i+3)
               graph[A[2*i+1]]=(2*i+1,2*i+2)
               graph[A[i+2*rank-4]]=(2*i,2*i+2)
          graph[A[3*rank-6]]=(2*rank-4,2*rank-3)
          graph[A[3*rank-5]]=(0,2*rank-3)
          graph[A[3*rank-4]]=(0,1)

          return GraphWithInverses(graph,A)


     @staticmethod
     def rose_graph(alphabet):
          """
          The rose graph labeled by the alphabet.

          The alphabet is copied.
          """
          graph=GraphWithInverses()
          graph._alphabet=alphabet.copy()

          for a in alphabet.positive_letters():
               graph.add_edge(0,0,[a,alphabet.inverse_letter(a)])
          return graph



class MetricGraph(GraphWithInverses):
     """
     Graph with edges labeled by an AlphabetWithInverses, with length on edges.
     """

     def length(self,a):
          pass
