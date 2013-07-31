#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
# 
#  Distributed under the terms of the GNU General Public License (GPL) 
#                  http://www.gnu.org/licenses/ 
#***************************************************************************** 
class MarkedGraph(GraphWithInverses):
     """
     A MarkedGraph is a GraphWithInverses together with a GraphMap
     which is a map from the rose to the graph.

     A ``MarkedGraph`` can be created from a ``GraphWithInverses`` by
     computing (randomly) a rose equivalent to the graph.

     EXAMPLES:

     sage: A=AlphabetWithInverses(3)
     sage: G=GraphWithInverses({'a':(0,0),'b':(0,1),'c':(1,0)},A)
     sage: print MarkedGraph(G)
     Marked graph:
     a: 0->0, b: 0->1, c: 1->0
     Marking: a->a, b->bc

     AUTHORS: 
 
     - Thierry Coulbois (2013-05-16): beta.0 version 
	 

     """

     def __init__(self,graph,marking=None):
         GraphWithInverses.__init__(self,graph,alphabet=graph._alphabet)
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
              
         self._marking=marking

     def __str__(self):
          result="Marked graph:\n"
          for a in self._alphabet.positive_letters(): 
               result=result+a+": {0}->{1}, ".format(self.initial_vertex(a),self.terminal_vertex(a))
          result=result[:-2]+"\n"
          result+="Marking: "
          for a in self._marking._domain._alphabet.positive_letters(): 
               result+=a+"->"+self._marking.image(a).__str__()+", "
          result=result[:-2]+"\n"

          return result

     def convex_core(self,other):
          return True
