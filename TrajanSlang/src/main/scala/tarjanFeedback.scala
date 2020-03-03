// #Sireum

import org.sireum._
import org.sireum.ops.{ISZOps, MSZOps, GraphOps}
import scala.collection.mutable.Stack


@record class TarjanGraphFeedback[A](src: ISZ[Edge[A]]) {

  type Index = Z

  @pure def inLoop(fromNode: A, targetNode: A, edges: ISZ[Edge[A]]): B = {
    //Connection from node we are searching from to targetNode
    edges.filter(e => e.from == fromNode && e.to.contains(targetNode)).nonEmpty ||
      Exists(edges.filter(e => e.from == fromNode).flatMap((x: Edge[A]) => x.to.elements))(newStartNode => inLoop(newStartNode, targetNode, edges))

    // Base case There is a direct edge from fromNode to target
    // \E e1, e2 \in nodes * e1 == e2 /\ Edge(e1,e2)

    // Inductive case - there is an edge that leads from any of the nodes that you can get to from the A(frontNode) back to A (target node)
    // \E
  }

  def allNodes(edges: ISZ[Edge[A]]): ISZ[A] = {
    var nodes = Set.empty[A] ++ (for (e <- edges) yield e.from)
    for (e <- edges.elements) {
      nodes.union(e.to)
    }
    return nodes.elements
  }

  val nodes: ISZ[A] = allNodes(src)

  //Linear over number of veritices and edges: O(V + E)
  @pure def tarjanAlgo(edges: ISZ[Edge[A]]): Set[ISZ[A]] = {
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
    var ret = Set.empty[ISZ[A]] //Keep track of SCC in graph
    val index: HashSMap[A, Index] = HashSMap.empty[A, Index] ++ (for (i <- nodes.indices) yield (nodes(i), i + 1))
    var lowLink: ISZ[Index] = index.values
    var exploredNodes = 0
    var stack = ISZ[A]() //Stack to keep track of nodes reachable from current node

    def visit(v: A): Unit = {
      stack = stack :+ (v)
      exploredNodes += 1
      for (w <- getSuccessors(v, edges)) {
        if (index.get(w).get > exploredNodes) {
          //Perform DFS from node W, if node w is not explored yet
          visit(w)
        }
        if (ISZOps(stack).contains(w)) {
          // and since node w is a neighbor to node v there is also a path from v to w
          val min = if (lowLink(index.get(w)) > index.get(v)) lowLink(v) else lowLink(v)
          //Remove old lowlink to replace it
          lowLink(v) = min
        }

        //The lowlink value haven't been updated meaning it is the root of a cycle/SCC
        if (lowLink(index.get(v)) == index.get(v)) {
          //Add the elements to the cycle that has been added to the stack and whose lowlink has been updated by node v's lowlink
          //This is the elements on the stack that is placed behind v
          val n = stack.size - ISZOps[A](stack).indexOf(v)
          ret += ISZOps[A](stack).takeRight(n)
          //Remove these elements from the stack
          stack = ISZOps[A](stack).dropRight(n)
        }
      }
    }

    //Perform a DFS from  all no nodes that hasn't been explored
    for (v <- nodes) {
      if (index.get(v).get > exploredNodes) {
        visit(v)
      }
    }
    return ret
  }

  //Todo write contract
  @pure def getSuccessors[A](v: A, edges: ISZ[Edge[A]]): ISZ[A] = {
    findEdge(v, edges) match {
      case Some(edge) => return edge.to.elements
      case None() => return ISZ[A]()
    }
  }

  //Todo write contract
  @pure def findEdge[A](v: A, edges: _root_.org.sireum.ISZ[Edge[A]]): Option[Edge[A]] = {
    for (e <- edges) {
      if (e.from == v) {
        return Some(e)
      }
    }
    return None()
  }

  val tarjan: Set[ISZ[A]] = tarjanAlgo(src)

  val hasCycle: B = ISZOps(tarjan.elements).exists(c => c.size >= 2)

  @strictpure def nodesInSystem(edges: ISZ[Edge[A]]): Z =
    (Set.empty[A] ++ edges.map((x: Edge[A]) => x.from) ++ edges.flatMap((x: Edge[A]) => x.to.elements)).size

}

