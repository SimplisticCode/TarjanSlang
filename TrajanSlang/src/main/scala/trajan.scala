// #Sireum

import org.sireum._
import org.sireum.ops.{ISZOps, MSZOps}

@datatype class Edge[A](from: A, to: Set[A])

@record class TarjanGraph[A](src: ISZ[Edge[A]]) {

  @pure def inLoop(fromNode: A, targetNode: A, edges: ISZ[Edge[A]]): Boolean = {
    //Connection from node we are searching from to targetNode
    ISZOps(edges).exists(e => e.from == fromNode && e.to == targetNode) ||
      Exists(edges.filter(e => e.from == fromNode).flatMap(x => x.to.elements))(newStartNode => inLoop(newStartNode, targetNode, edges))

    // Base case There is a direct edge from fromNode to target
    // \E e1, e2 \in nodes * e1 == e2 /\ Edge(e1,e2)

    // Inductive case - there is an edge that leads from any of the nodes that you can get to from the A(frontNode) back to A (target node)
    // \E
  }

  //Linear over number of veritices and edges: O(V + E)
  @pure def tarjanAlgo(edges: ISZ[Edge[A]]): MSZ[MSZ[A]] = {
    Contract(
      Case("No loops in graph",
        Requires(
          edges.nonEmpty &&
            //It is fine to only look at from nodes since all other vertices in graph
            //does not have an outgoing edge
            !Exists(edges.map(x => x.from))(x => inLoop(x, x, edges))),
        Ensures(
          //A list inside the nested result list should have a length of one (No SCC)
          All(Res[MSZ[MSZ[A]]])(l => l.size == Z(1)) &&
          // All elements in the list should be unique
            Z(Res[MSZ[MSZ[A]]].elements.distinct.length) == Res[MSZ[MSZ[A]]].length &&
            //The outer list of the result list should have the same length as the number of nodes in the graph
            Res[MSZ[MSZ[A]]].length == (Set.empty[A] ++ edges.map(x => x.from) ++ edges.flatMap(x => x.to.elements)).size
        )
      ),
      Case("Loops in graph",
        Requires(
          edges.nonEmpty &&
            //It is fine to only look at from nodes since all other vertices in graph
            //does not have an outgoing edge
            //There should exist at least one node that is a part of a loop
            Exists(edges.map(x => x.from))(x => inLoop(x, x, edges))),
        Ensures()
      )
      //Ensures(All(Res[MSZ[MSZ[A]]].flatMap(x => x.asInstanceOf[MSZ[A]]))(e => edges.elements.contains(e)))
      //Ensures(All(Res[MSZ[MSZ[A]]].indices)(i => All(Res[MSZ[MSZ[A]]](i).indices)(j => Exists(edges.elements.combinations().indices)(e => e))))
      //Res[MSZ[MSZ[A]]](i).indices)(j => )))
      //Ensures(All(Res[MSZ[MSZ[A]]].elements)(e => e.))
    )
    var s = MSZ[A]() //Stack to keep track of nodes reachable from current node
    var index = Map.empty[A, Z] //index of each node
    var lowLink = Map.empty[A, Z] //The smallest index reachable from the node
    var ret = MSZ[MSZ[A]]() //Keep track of SCC in graph

    def visit(v: A): Unit = {
      //Set index and lowlink of node on first visit
      index = index + (v ~> index.size)
      lowLink = lowLink + (v ~> index.get(v).get)

      //Add to stack
      s = s ++ MSZ(v)

      edges.filter(o => o.from == v).flatMap(o => o.to.elements).foreach(w => {
        if (!index.contains(w)) {
          //Perform DFS from node W, if node w is not explored yet
          visit(w)
        }
        if (s.elements.contains(w)) {
          // and since node w is a neighbor to node v there is also a path from v to w

          val min = math.min(lowLink.get(w).get.toInt, lowLink.get(v).get.toInt)
          //Remove old lowlink to replace it
          lowLink = lowLink - (v ~> lowLink.get(v).get.toInt)
          lowLink = lowLink + (v ~> min)
        }
      })

      //The lowlink value haven't been updated meaning it is the root of a cycle/SCC
      if (lowLink.get(v) == index.get(v)) {
        //Add the elements to the cycle that has been added to the stack and whose lowlink has been updated by node v's lowlink
        //This is the elements on the stack that is placed behind v
        val n = s.length - s.elements.indexOf(v)
        ret = ret :+ (MSZOps[A](s).takeRight(n))
        //Remove these elements from the stack
        s = MSZOps[A](s).dropRight(n)
      }
    }

    //Perform a DFS from  all no nodes that hasn't been explored
    src.foreach(v => if (!index.contains(v.from)) visit(v.from))
    return ret
  }


  val tarjan: MSZ[MSZ[A]] = tarjanAlgo(src)

  val hasCycle: Boolean = tarjan.elements.exists(c => c.size >= 2)
  val tarjanCycle: Seq[MSZ[A]] = tarjan.elements.filter(c => c.size >= 2).distinct.map(c => c)
  /*
    lazy val topologicalSort: IODependencyResult =
      if (hasCycle) IODependencyCyclic(trajanCycle.map(o=> o.reverse.mkString("Cycle: "," -> ", " -> " + o.reverse.head.toString)).mkString("\n"))
      else IODependencyAcyclic(trajan.flatten.reverse.map(_.asInstanceOf[ConnectionScalarVariable]).toList)

   */
}

