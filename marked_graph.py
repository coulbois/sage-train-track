#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from inverse_graph import GraphWithInverses, MetricGraph
from graph_map import GraphMap
from sage.combinat.words.morphism import WordMorphism

class MarkedGraph(GraphWithInverses):
     """
     A MarkedGraph is a GraphWithInverses together with a GraphMap
     which is a map from the rose to the graph.

     A ``MarkedGraph`` can be created from a ``GraphWithInverses`` by
     computing (randomly) a rose equivalent to the graph.

     EXAMPLES::

     sage: G=GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)})
     sage: print MarkedGraph(G)
     Marked graph:
     a: 0->0, b: 0->1, c: 1->0
     Marking: a->a, b->bc

     AUTHORS:

     - Thierry Coulbois (2013-05-16): beta.0 version
     """
     def __init__(self,graph=None,marking=None,alphabet=None,marking_alphabet=None):
         if isinstance(marking,GraphMap):
              GraphWithInverses.__init__(self,marking.codomain(),marking.codomain().alphabet())
              self._marking=marking
         else:
              if isinstance(graph,GraphWithInverses):
                   alphabet=graph._alphabet
              GraphWithInverses.__init__(self,graph,alphabet)

              if marking is None: #computes a (random) marking from a rose equivalent to graph

                   A=graph.alphabet()
                   tree=graph.spanning_tree()

                   j=0
                   letter=dict()
                   for a in A.positive_letters():
                        vi=graph.initial_vertex(a)
                        vt=graph.terminal_vertex(a)
                        if (len(tree[vi])==0 or tree[vi][-1]!=A.inverse_letter(a)) and\
                                 (len(tree[vt])==0 or tree[vt][-1]!=a):
                             letter[j]=a
                             j=j+1



                   B=AlphabetWithInverses(j)
                   RB=GraphWithInverses.rose_graph(B)

                   edge_map=dict()

                   for i in xrange(j):
                        a=letter[i]
                        edge_map[B[i]]=graph.reduce_path(tree[graph.initial_vertex(a)]\
                                                           *Word([a])\
                                                           *graph.reverse_path(tree[graph.terminal_vertex(a)]))

                        marking=GraphMap(RB,graph,edge_map)
              else:
                   marking=GraphMap(GraphWithInverses.rose_graph(marking_alphabet),self,marking)
              self._marking=marking

     def __str__(self):
          """
          String representation of ``self``.
          """
          result="Marked graph: "
          for a in self._alphabet.positive_letters():
               result=result+a+": {0}->{1}, ".format(self.initial_vertex(a),self.terminal_vertex(a))
          result=result[:-2]+"\n"
          result+="Marking: "
          for a in self._marking._domain._alphabet.positive_letters():
               result+=a+"->"+self._marking.image(a).__str__()+", "
          result=result[:-2]

          return result

     def marking(self):
          """
          A ``GraphMap`` from the rose to ``self``.
          """
          return self._marking

     def precompose(self,automorphism):
          """
          Precompose the marking by ``automorphism``.
          """
          edge_map=dict()
          for a in self._marking.domain().alphabet().positive_letters():
               edge_map[a]=self._marking(automorphism.image(a))
          self._marking.set_edge_map(edge_map)
          return self


     def difference_of_marking(self,other):
          """
          A ``GraphMap`` from ``self`` to ``other`` that makes the markings commute.
          """

          return other.marking()*self.marking().inverse()


     def subdivide(self,edge_list):
          """
          Subdivides edges in the edge_list into two edges.

          WARNING:

          each edge in ``edge_list`` must appear only once.

          SEE ALSO:

          ``GraphWithInverses.subdivide()``
          """

          subdivide_map=GraphWithInverses.subdivide(self,edge_list)
          subdivide_morph=WordMorphism(subdivide_map)
          self._marking.set_edge_map(subdivide_morph*self._marking._edge_map)
          return subdivide_map

     def fold(self,edges_full,edges_partial):
          """
          Folds the edges.

          OUTPUT:

          A dictionnary that maps old edges to new graph paths.

          SEE ALSO:

          ``GraphWithInverses.fold()``
          """

          fold_map=GraphWithInverses.fold(self,edges_full,edges_partial)
          fold_morph=WordMorphism(fold_map)
          self._marking.set_edge_map(fold_morph*self._marking._edge_map)
          return fold_map

     def contract_forest(self,forest):
          """
          Contract the forest.

          OUTPUT:

          A dictionnary that maps old edges to new edges.

          SEE ALSO:

          ``GraphWithInverses.contract_forest()``
          """

          contract_map=GraphWithInverses.contract_forest(self,forest)
          contract_morph=WordMorphism(contract_map)
          self._marking.set_edge_map(contract_morph*self._marking._edge_map)
          return contract_map

     @staticmethod
     def rose_marked_graph(alphabet):
          """
          The rose on ``alphabet`` marked with the identity.
          """

          marking=dict((a,a) for a in alphabet.positive_letters())
          return MarkedGraph(graph=GraphWithInverses.rose_graph(alphabet),marking=marking,marking_alphabet=alphabet)




class MarkedMetricGraph(MarkedGraph,MetricGraph):
     """
     A ``MarkedGraph`` together with a length function on edges.

     EXAMPLES::

     sage: G=MarkedMetricGraph({'a':(0,0),'b':(0,1),'c':(1,0)})
     Marked metric graph:
     a: 0->0, b: 0->1, c: 1->0
     Marking: a->a, b->bc
     Length: a: 1, b: 1, c: 1
     """
     def __init__(self,graph=None,marking=None,length=None,alphabet=None,marking_alphabet=None):
          MarkedGraph.__init__(self,graph=graph,marking=marking,alphabet=alphabet,marking_alphabet=marking_alphabet)

          if length is None:
               length=dict((a,1) for a in self.alphabet())
          else:
               for a in length.keys():
                    length[self.alphabet().inverse_letter(a)]=length[a]

          self._length=length


     def __str__(self):
          """
          String representation for ``self``.
          """
          result=MarkedGraph.__str__(self)+"\n"
          result+="Length: "
          for a in self.alphabet().positive_letters():
               result+=a+":{0}".format(self.length(a))+", "
          result=result[:-2]
          return result


     def length(self,a):
          """
          The length of the edge labeled by ``a``
          """
          return self._length[a]

     def set_length(self,a,l):
          """
          Sets the length of the edge ``a`` to ``l``.
          """
          length[a]=l
          length[self.alphabet().inverse_letter(a)]=l



     @staticmethod
     def splitting(i,A):
          """
          The ``MarkedMetricGraph`` that corresponds to the splitting
          ``F(A)=F(A[:i])*F(A[i:])``.

          This is a graph with two vertices linked by an edge e and a
          loop for each letter in A. Letters in A[:i] are attached to
          the first vertex while letters in A[:i] are attached to the
          second vertex.

          All loops have length 0, the splitting edge ``e`` has length
          1.
          """

          graph=dict()
          length=dict()
          marking=dict()

          B=A.copy()
          [e,ee]=B.add_new_letter()

          for j in xrange(i):
               a=A[j]
               graph[a]=(0,0)
               length[a]=0
               marking[a]=Word([a])

          for j in xrange(i,len(A)):
               a=A[j]
               graph[a]=(1,1)
               length[a]=0
               marking[a]=Word([e,a,ee])

          graph[e]=(0,1)
          length[e]=1

          return MarkedMetricGraph(graph,marking,length,B,A)

     @staticmethod
     def HNN_splitting(A):
          """
          The marked metric graph corresponding to the HNN splitting
          F_N=F_{N-1}*<t>.

          The rose marked graph with all edges of length 0 except ``A[0]``
          which is of length 1.
          """

          length=dict((a,0) for a in A.positive_letters())
          length[A[0]]=1

          RA=GraphWithInverses.rose_graph(A)
          RAA=GraphWithInverses.rose_graph(A)
          marking=GraphMap(RA,RAA,edge_map=dict((a,Word([a])) for a in A.positive_letters()))

          return MarkedMetricGraph(marking=marking,length=length)
