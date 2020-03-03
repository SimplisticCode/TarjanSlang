// #Sireum

import org.sireum._
import org.sireum.ops.ISZOps


@record class TarjanGraphFeedback[A](src: ISZ[Edge[A]]) {
  type Index = Z

  @pure def inLoop(fromNode: Index, targetNode: Index): B = {
    //Connection from node we are searching from to targetNode
    val neighbours: ISZ[Index] = edges.get(fromNode) match {
      case Some(neighbours) => neighbours.elements
      case _ => return F
    }

    return ISZOps(neighbours).contains(targetNode) || Exists(neighbours)(newStart => inLoop(newStart, targetNode))

    // Base case There is a direct edge from fromNode to target
    // \E e1, e2 \in nodes * e1 == e2 /\ Edge(e1,e2)

    // Inductive case - there is an edge that leads from any of the nodes that you can get to from the A(frontNode) back to A (target node)
    // \E
  }

  def allNodes(edges: ISZ[Edge[A]]): HashSMap[A, Index] = {
    var nodes = Set.empty[A] ++ (for (e <- edges) yield e.from)
    for (e <- edges.elements) {
      nodes = nodes.union(e.to)
    }
    return HashSMap.empty[A, Index] ++ (for (i <- nodes.elements.indices) yield (nodes.elements(i), i + 1))
  }

  val nodes: HashSMap[A, Index] = allNodes(src)
  val nodesInverse: HashSMap[Index, A] = HashSMap.empty[Index, A] ++ (for (n <- nodes.entries) yield (n._2, n._1))
  val edges: HashSMap[Index, HashSSet[Z]] = transformEdges(src)

  def transformEdges(src: _root_.org.sireum.ISZ[Edge[A]]): HashSMap[Index, HashSSet[Index]] = {
    var e = HashSMap.empty[Index, HashSSet[Index]]
    time {
      e = HashSMap.empty[Index, HashSSet[Index]] ++ (for (e <- src) yield ((nodes.get(e.from).get, HashSSet.empty[Index] ++ (for (i <- e.to.elements) yield (nodes.get(i).get)))))
    }
    return e
  }

  def time[R](block: => R): R = {
    val t0 = System.nanoTime()
    val result = block // call-by-name
    val t1 = System.nanoTime()
    println("Elapsed time: " + (t1 - t0).toString + "ns")
    return result
  }


  //Linear over number of veritices and edges: O(V + E)
  @pure def tarjanAlgo(): Set[ISZ[A]] = {
    /*
    Contract(
      Case("No loops in graph",
        Requires(
          edges.nonEmpty &&
            //It is fine to only look at from nodes since all other vertices in graph
            //does not have an outgoing edge
            !Exists(edges.map(x => x.from))(x => inLoop(x, x, edges))),
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
            Exists(edges.map(x => x.from))(x => inLoop(x, x, edges))),
        Ensures(
          //All elements in a nested list (SCC) with a length >= 2 should be a part of a loop
          All(Res[MSZ[MSZ[A]]].filter(x => x.size >= 2).flatMap((x: MSZ[A]) => x))(e => inLoop(e, e, edges)) &&
            //All elements that a not a part of a SCC (length < 2) should not be in a loop
            All(Res[MSZ[MSZ[A]]].filter(x => x.size < 2).flatMap((x: MSZ[A]) => x))(e => !inLoop(e, e, edges)) &&
            //All nodes in the graph should be represented in the final result
            nodesInSystem(edges) == Res[MSZ[MSZ[A]]].flatMap((x: MSZ[A]) => x).size
            //All elements in a loop/SCC should  be strongly connected with each other.
            && All(Res[MSZ[MSZ[A]]].filter(x => x.size >= 2))(s => All(s)(e1 => All(s.filter(e => e != e1))(e2 => inLoop(e1, e2, edges))))
          // TODO: Add post condition to make sure that all loops in the graph have been detected
          //  this means that the right numbers of loops/SCC (length >= 2) are found and put in the result
        )
      )
    )
     */
    var ret = Set.empty[ISZ[Index]] //Keep track of SCC in graph
    var lowLink: HashSMap[Index, Index] = HashSMap.empty[Index, Index]
    time {
      lowLink = HashSMap.empty[Index, Index] ++ (for (n <- nodes.values) yield (n, n))
    }
    var exploredNodes: Z = 0
    var stack = ISZ[Index]()

    def visit(v: Index): Unit = {
      stack = stack :+ (v)
      exploredNodes += 1
      for (w <- getSuccessors(v)) {
        if (w > exploredNodes) {
          //Perform DFS from node W, if node w is not explored yet
          visit(w)
        }
        if (ISZOps(stack).contains(w)) {
          // and since node w is a neighbor to node v there is also a path from v to w
          val min = findMinLowlink(w, v, lowLink)
          //Remove old lowlink to replace it
          lowLink = lowLink + (v ~> min)
        }
      }
      //The lowlink value haven't been updated meaning it is the root of a cycle/SCC
      if (lowLink.get(v).get == v) {
        //Add the elements to the cycle that has been added to the stack and whose lowlink has been updated by node v's lowlink
        //This is the elements on the stack that is placed behind v
        val n = stack.size - ISZOps[Index](stack).indexOf(v)
        ret += ISZOps[Index](stack).takeRight(n)
        //Remove these elements from the stack
        stack = ISZOps[Index](stack).dropRight(n)
      }
    }

    //Perform a DFS from  all no nodes that hasn't been explored
    for (v <- nodes.entries) {
      if (nodes.get(v._1).get > exploredNodes) {
        visit(v._2)
      }
    }

    return Set.empty[ISZ[A]] ++ (for (e <- ret.elements) yield (for (i <- e) yield nodesInverse.get(i).get))

  }

  def getSuccessors(v: Index): ISZ[Index] = {
    edges.get(v) match {
      case Some(n) => return n.elements
      case _ => return ISZ[Index]()
    }
  }

  //TODO Contract
  @pure def findMinLowlink(w: Index, v: Index, lowLink: HashSMap[Index, Index]): Index = {
    if (lowLink.get(w).get > lowLink.get(v).get) {
      return lowLink.get(v).get
    } else {
      return lowLink.get(w).get
    }
  }

  @pure def size: Z = {
    return nodes.size
  }

  val tarjan: Set[ISZ[A]] = tarjanAlgo()

  val tarjanCycle: ISZ[ISZ[A]] = tarjan.elements.filter(c => c.size >= 2)

  val hasCycle: B = ISZOps(tarjan.elements).exists(c => c.size >= 2)


  def topologicalSort(): ISZ[A] = {
    Contract(
      Case("Graph contains cycles so a topological ordering cannot be found. The function shall instead return a list with all the SCC/loops",
        Requires(
          edges.nonEmpty &&
            Exists(edges.getKeys)(x => inLoop(x, x))),
        Ensures(Res[ISZ[A]].isEmpty)
      ),
      Case("Graphs contains no loops",
        Requires(
          edges.nonEmpty &&
            !Exists(edges.getKeys)(x => inLoop(x, x))),
        Ensures(
          //There should be no element at an index > n, that has a connection to a component placed at index n
          All(Res[ISZ[A]].indices)(n => !Exists(Res[ISZ[A]].indices)(j => j > n && inLoop(nodes.get(Res[ISZ[A]](j)).get, nodes.get(Res[ISZ[A]](n)).get)) &&
            //All elements/vertices in the graph should be in the resulting list
            Res[MSZ[MSZ[A]]].size == size
          )
        )
      )
    )

    if (hasCycle) {
      return ISZ[A]()
    }
    else {
      return ISZOps(tarjan.elements.flatMap(x => x)).reverse
      //return ISZOps(for (s <- tarjan.elements) yield (for (e <- s) yield (e))).reverse
    }
  }
}

