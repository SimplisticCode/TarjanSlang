// #Sireum

import org.sireum._
import org.sireum.ops.{ISZOps, MSZOps}

@record class TarjanGraphMapsAsEdges[A](src: Map[A, Set[A]]) {

  @pure def inLoop(fromNode: A, targetNode: A, edges: Map[A, Set[A]]): B = {
    //Connection from node we are searching from to targetNode
    edges.entries.filter((edge) => edge._1 == fromNode && edge._2.contains(targetNode)).nonEmpty ||
      Exists(edges.entries.filter((edge) => edge._1 == fromNode).flatMap((edge) => edge._2.elements))(newStartNode => inLoop(newStartNode, targetNode, edges))

    // Base case There is a direct edge from fromNode to target
    // \E e1, e2 \in nodes * e1 == e2 /\ Edge(e1,e2)

    // Inductive case - there is an edge that leads from any of the nodes that you can get to from the A(frontNode) back to A (target node)
    // \E
  }

  //Linear over number of veritices and edges: O(V + E)
  @pure def tarjanAlgo(edges: Map[A, Set[A]]): MSZ[MSZ[A]] = {
    Contract(
      Case("No loops in graph",
        Requires(
          edges.nonEmpty &&
            //It is fine to only look at from nodes since all other vertices in graph
            //does not have an outgoing edge
            !Exists(edges.keys)(x => inLoop(x, x, edges))),
        Ensures(
          //A list inside the nested result list should have a length of one (No SCC)
          All(Res[MSZ[MSZ[A]]])(l => l.size == 1) &&
            // All elements in the list should be unique
            (Set.empty[A] ++ (Res[MSZ[MSZ[A]]].flatMap((x: MSZ[A]) => x)).toIS).size == Res[MSZ[MSZ[A]]].size &&
            //The outer list of the result list should have the same length as the number of nodes in the graph
            Res[MSZ[MSZ[A]]].size == nodesInSystem(edges)
        )
      ),
      Case("Loops in graph",
        Requires(
          edges.nonEmpty &&
            //There should exist at least one node that is a part of a loop<
            Exists(edges.keys)(x => inLoop(x, x, edges))),
        Ensures(
          //All elements in a nested list (SCC) with a length >= 2 should be a part of a loop
          All(Res[MSZ[MSZ[A]]].filter(x => x.size >= 2).flatMap((x: MSZ[A]) => x))(e => inLoop(e, e, edges)) &&
            //All elements that a not a part of a SCC (length < 2) should not be in a loop
            All(Res[MSZ[MSZ[A]]].filter(x => x.size < 2).flatMap((x: MSZ[A]) => x))(e => !inLoop(e, e, edges)) &&
            //All nodes in the graph should be represented in the final result
            nodesInSystem(edges) == Res[MSZ[MSZ[A]]].flatMap((x: MSZ[A]) => x).size
          // TODO: Add post condition to make sure that all loops in the graph have been detected
          //  this means that the right numbers of loops/SCC (length >= 2) are found and put in the result
        )
      )
    )
    val n = nodesInSystem(edges)
    var s = MSZ[A]() //Stack to keep track of nodes reachable from current node
    var index = Map.empty[A, Z] //index of each node
    var lowLink: MSZ[Z] = MSZ.create(n, 100) //The smallest index reachable from the node
    var ret = MSZ[MSZ[A]]() //Keep track of SCC in graph

    def visit(v: A): Unit = {
      //Set index and lowlink of node on first visit
      index += (v ~> index.size)
      lowLink(index.get(v).get) = index.get(v).get

      //Add to stack
      s = s :+ v

      edges.entries.filter(o => o._1 == v).flatMap(o => o._2.elements).foreach(w => {
        if (!index.contains(w)) {
          //Perform DFS from node W, if node w is not explored yet
          visit(w)
        }
        if (s.elements.contains(w)) {
          // and since node w is a neighbor to node v there is also a path from v to w
          val min = minLowlink(index, lowLink, v, w)
          //Remove old lowlink to replace it
          lowLink(index.get(v).get) = min
        }
      })

      //The lowlink value haven't been updated meaning it is the root of a cycle/SCC
      if (lowLink(index.get(v).get) == index.get(v).get) {
        //Add the elements to the cycle that has been added to the stack and whose lowlink has been updated by node v's lowlink
        //This is the elements on the stack that is placed behind v
        val n = s.size - MSZOps[A](s).indexOf(v)
        ret = ret :+ (MSZOps[A](s).takeRight(n))
        //Remove these elements from the stack
        s = MSZOps[A](s).dropRight(n)
      }
    }

    //Perform a DFS from  all no nodes that hasn't been explored
    edges.keys.foreach(v => if (!index.contains(v)) visit(v))
    return ret
  }


  @pure def minLowlink(index: Map[A, Z], lowLink: MSZ[Z], v: A, w: A): Z = {
    Contract(
      Requires(
        //Index should contain the two keys
        index.contains(v) && index.contains(w) &&
          //All values of the range of index should be a valid index for lowlink
          All(index.values)((rangeVal: Z) => ISZOps(lowLink.indices).contains(rangeVal))),
      Ensures(Res[Z] <= lowLink(index.get(w).get) && Res[Z] <= lowLink(index.get(v).get))
    )
    if (lowLink(index.get(v).get) > lowLink(index.get(w).get)) {
      return lowLink(index.get(w).get)
    } else {
      return lowLink(index.get(v).get)
    }
  }

  @strictpure def nodesInSystem(edges: Map[A, Set[A]]): Z =
    (Set.empty[A] ++ edges.keys ++ edges.values.flatMap(x => x.elements)).size

  val tarjan: MSZ[MSZ[A]] = tarjanAlgo(src)

  val hasCycle: B = tarjan.elements.exists(c => c.size >= 2)
  val tarjanCycle: Seq[MSZ[A]] = tarjan.elements.filter(c => c.size >= 2).distinct.map(c => c)

  def topologicalSort(edges: Map[A, Set[A]]): ISZ[A] = {
    Contract(
      Case("Graph contains cycles so a topological ordering cannot be found. The function shall instead return a list with all the SCC/loops",
        Requires(
          edges.nonEmpty &&
            Exists(edges.keys)(x => inLoop(x, x, edges))),
          Ensures(Res[ISZ[A]].isEmpty)
        ),
        Case("Graphs contains no loops",
          Requires(
            edges.nonEmpty &&
              !Exists(edges.keys)(x => inLoop(x, x, edges))),
          Ensures(
            //There should be no element at an index > n, that has a connection to a component placed at index n
            All(Res[ISZ[A]].indices)(n => !Exists(Res[ISZ[A]].indices)(j => j > n && inLoop(Res[ISZ[A]](j), Res[ISZ[A]](n), edges))) &&
              //All elements/vertices in the graph should be in the resulting list
              Res[MSZ[MSZ[A]]].size == nodesInSystem(edges)
          )
        )
      )
    if (hasCycle){
      return ISZ[A]()
    }
    else {
      return MSZOps(tarjan.flatMap(x => x)).reverse.toIS
    }
  }
}

