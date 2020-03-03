// #Sireum

import org.sireum._
import org.sireum.ops.{ISZOps, MSZOps}

@datatype class Edge[A](from: A, to: Set[A])

@record class TarjanGraphLogika[A](src: ISZ[Edge[A]]) {

  @pure def inLoop(fromNode: A, targetNode: A, edges: ISZ[Edge[A]]): B = {
    //Connection from node we are searching from to targetNode
    edges.filter(e => e.from == fromNode && e.to.contains(targetNode)).nonEmpty ||
      Exists(edges.filter(e => e.from == fromNode).flatMap((x: Edge[A]) => x.to.elements))(newStartNode => inLoop(newStartNode, targetNode, edges))

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
            !Exists(edges.map((x: Edge[A]) => x.from))(x => inLoop(x, x, edges))),
        Ensures(
          //A list inside the nested result list should have a length of one (No SCC)
          All(Res[MSZ[MSZ[A]]])(l => l.size == 1) &&
            // All elements in the list should be unique
            (Set.empty[A] ++ (Res[MSZ[MSZ[A]]].flatMap((x: MSZ[A]) => x)).toIS).size == Res[MSZ[MSZ[A]]].size &&
            //The outer list of the result list should have the same length as the number of nodes in the graph
            Res[MSZ[MSZ[A]]].size == nodesInSystem(edges)

          //It would be very convenient if I shouldn't declare the type of Res all the time..
        )
      ),
      Case("Loops in graph",
        Requires(
          edges.nonEmpty &&
            //There should exist at least one node that is a part of a loop<
            Exists(edges.map((x: Edge[A]) => x.from))(x => inLoop(x, x, edges))),
        Ensures(
          //All elements in a nested list (SCC) with a length >= 2 should be a part of a loop
          All(Res[MSZ[MSZ[A]]].filter(x => x.size >= 2).flatMap((x: MSZ[A]) => x))(e => inLoop(e, e, edges)) &&
            //All elements that a not a part of a SCC (length < 2) should not be in a loop
            All(Res[MSZ[MSZ[A]]].filter(x => x.size < 2).flatMap((x: MSZ[A]) => x))(e => !inLoop(e, e, edges)) &&
            //All nodes in the graph should be represented in the final result
            nodesInSystem(edges) == Res[MSZ[MSZ[A]]].flatMap((x: MSZ[A]) => x).size
        )
      )
    )
    var s = MSZ[A]() //Stack to keep track of nodes reachable from current node
    var index = Map.empty[A, Z] //index of each node
    var lowLink: MSZ[Z] = MSZ.create(nodesInSystem(edges), 100) //The smallest index reachable from the node
    //The smallest index reachable from the node
    var ret = MSZ[MSZ[A]]() //Keep track of SCC in graph

    def visit(v: A): Unit = {
      //Set index and lowlink of node on first visit
      index = index + (v ~> index.size)
      lowLink(index.get(v).get) = index.get(v).get

      //Add to stack
      s = s ++ MSZ(v)

      edges.filter((o: Edge[A]) => o.from == v).flatMap((o: Edge[A]) => o.to.elements).foreach((w: A) => {
        if (!index.contains(w)) {
          //Perform DFS from node W, if node w is not explored yet
          visit(w)
          val min: Z = minLowlink(index, lowLink, v, w)
          lowLink(index.get(v).get) = min
        }
        else if (s.filter(e => e == w).nonEmpty) {
          // and since node w is a neighbor to node v there is also a path from v to w
          val min: Z = minLowlink(index, lowLink, v, w)
          lowLink(index.get(v).get) = min
        } else {
          // Logika requires me to have an else-case. Can I prevent this?
          val a: Z = 2
          assert(a == 2)
        }
      })

      //The lowlink value haven't been updated meaning it is the root of a cycle/SCC
      if (lowLink.get(v) == index.get(v)) {
        //Add the elements to the cycle that has been added to the stack and whose lowlink has been updated by node v's lowlink
        //This is the elements on the stack that is placed behind v
        val n = s.size - MSZOps[A](s).indexOf(v)
        ret = ret :+ (MSZOps[A](s).takeRight(n))
        //Remove these elements from the stack
        s = MSZOps[A](s).dropRight(n)
      }
    }


    //Perform a DFS from  all no nodes that hasn't been explored
    src.foreach((v: Edge[A]) =>
      if (!index.contains(v.from)) {
        visit(v.from)
      } else {
        val a: Z = 2
        assert(a == 2)
      })
    return ret
  }

  //I couldn't verify this function
  @pure def minLowlink(index1: Z, index2: Z, lowLink: ISZ[Z]): Z = {
    Contract(
      Requires(
        //Index should contain the two keys
        lowLink.size > index1,
          index1 >= 0,
          lowLink.size > index2,
          index2 >= 0
        //Exists(lowLink.indices)(i => i == index1) &&
          //Exists(lowLink.indices)(i => i == index2)
          //All values of the range of index should be a valid index for lowlink
      )
      , Ensures(Res[Z] <= lowLink(index1) && Res[Z] <= lowLink(index2))
    )
    if (lowLink(index1) > lowLink(index2)) {
      return lowLink(index2)
    } else {
      return lowLink(index1)
    }
  }

  @strictpure def nodesInSystem(edges: ISZ[Edge[A]]): Z =
    return (Set.empty[A] ++ edges.map((x: Edge[A]) => x.from) ++ edges.flatMap((x: Edge[A]) => x.to.elements)).size
}