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

     AUTHORS: 
 
     - Thierry Coulbois (2013-05-16): beta.0 version 
	 

     """

     def __init__(self,graph,marking):
         GraphWithInverses.__init__(self,graph)
         self._marking=marking

     def __str__(self):
          result="Marked graph:\n"
          result+=self._marking.__str__()+"\n"
          return result

     def convex_core(self,other):
          return True
