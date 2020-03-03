import org.scalatest.{FlatSpec, Matchers}
import org.sireum._
import org.sireum.ops.ISZOps

import scala.annotation.tailrec

class TarjanAlgorithmMapsAsEdges extends FlatSpec with Matchers {
  val set1: Set[Z] = Set.empty ++ ISZ(2)
  val set2: Set[Z] = Set.empty ++ ISZ(3)
  val set3: Set[Z] = Set.empty ++ ISZ(4)
  val set4: Set[Z] = Set.empty ++ ISZ(1)
  val allEdges: Map[Z, Set[Z]] = Map.empty ++ ISZ((1, set1), (2, set2), (3, set3), (4, set4))

  @tailrec
  private def generateMapEdges(n: Z, edges: Map[Z, Set[Z]] = Map.empty[Z, Set[Z]]()): Map[Z, Set[Z]] = {
    if (n == Z(0)) edges
    else generateMapEdges(n - 1, edges + ((n - 1) ~> (Set.empty ++ ISZ(n))))
  }

  @tailrec
  private def generateMapEdgesDec(n: Z, edges: Map[Z, Set[Z]] = Map.empty[Z, Set[Z]]()): Map[Z, Set[Z]] = {
    if (n == Z(0)) edges
    else generateMapEdgesDec(n - 1, edges + ((n ~> (Set.empty ++ ISZ(n - 1)))))
  }

  "Tarjan " should "report an algebraic loop" in {
    val g = new TarjanGraphMapsAsEdges[Z](allEdges)
    assert(g.hasCycle)
    assert(g.tarjanCycle.size == 1)
  }

  "Tarjan Graph with two loops" should "report two algebraic loops" in {
    //Not the edge from 4 -> 1 needs to be added again otherwise it will be overwritten
    val edges: Map[Z, Set[Z]] = allEdges ++ ISZ((4, (Set.empty[Z] ++ ISZ(5,1))), (5, (Set.empty[Z] ++ ISZ(6))),
      (6, (Set.empty[Z] ++ ISZ(7))), (7, (Set.empty[Z] ++ ISZ(5))))
    val g = new TarjanGraphMapsAsEdges[Z](edges)
    assert(g.hasCycle)
    assert(g.tarjanCycle.size == 2)
  }

  "Tarjan Graph with three loops" should "report three algebraic loops" in {
    //Not the edge from 4 -> 1 needs to be added again otherwise it will be overwritten
    val edges = allEdges ++ ISZ((4, Set.empty ++ ISZ(1, 5)), (5, Set.empty[Z] ++ ISZ(6)),
      (6, Set.empty ++ ISZ(5, 7)), (8, Set.empty ++ ISZ(7)), (7, Set.empty ++ ISZ(8)))
    val g = new TarjanGraphMapsAsEdges[Z](edges)
    assert(g.hasCycle)
    assert(g.tarjanCycle.size == 3)
    //val sort = g.topologicalSort

  }

  "Tarjan BigGrahp 100+ edges" should "report AN algebraic loop" in {
    val alotOfEdges = generateMapEdges(100) + (100 ~> (Set.empty ++ ISZ(1)))
    val g = new TarjanGraphMapsAsEdges[Z](alotOfEdges)
    assert(g.hasCycle)
  }

  "Tarjan BigGrahp 10000+ edges" should "report AN algebraic loop" in {
    val alotOfEdges = generateMapEdges(10000) + (10000 ~> (Set.empty ++ ISZ(1)))
    val g = new TarjanGraphMapsAsEdges[Z](alotOfEdges)
    assert(g.hasCycle)
  }

  "Tarjan BigGrahp 1000+ edges" should "report NO algebraic loop" in {
    val alotOfEdges = generateMapEdges(1001)
    val g = new TarjanGraphMapsAsEdges[Z](alotOfEdges)
    assert(!g.hasCycle)
  }

  def time[R](block: => R): R = {
    val t0 = System.nanoTime()
    val result = block // call-by-name
    val t1 = System.nanoTime()
    println("Elapsed time: " + (t1 - t0) + "ns")
    result
  }

  "Tarjan BigGrahp 100000+ edges" should "report NO algebraic loop" ignore {
    val alotOfEdges = generateMapEdges(100000)
    time {
      val g = new TarjanGraphMapsAsEdges[Z](alotOfEdges)
      assert(!g.hasCycle)
    }
  }

  "Topological sort" should "report that no topological order can be found~> Since there is a loop in the graph" in {
    val g = new TarjanGraphMapsAsEdges[Z](allEdges)
    assert(g.hasCycle)
    val order = g.topologicalSort(allEdges)
    assert(order.isEmpty)
  }

  "Topological sort" should "report the topological order of the graph (The topological order is ascending)" in {
    val edges = generateMapEdges(11)
    val g = new TarjanGraphMapsAsEdges[Z](edges)
    assert(!g.hasCycle)
    val order = g.topologicalSort(edges)
    assert(order.nonEmpty)
    val expectedTopologicalOrder = ISZ[Z](0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)
    assert(order == expectedTopologicalOrder)
  }

    "Topological sort" should "report the topological order of the graph (The topological order is descending)" in {
      val edges = generateMapEdgesDec(11)
      val g = new TarjanGraphMapsAsEdges[Z](edges)
      assert(!g.hasCycle)
      val order = g.topologicalSort(edges)
      assert(order.nonEmpty)
      val expectedTopologicalOrder = ISZOps(ISZ[Z](0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)).reverse
      assert(order == expectedTopologicalOrder)
    }

    "Topological sort on a more advanced graph" should "report the topological order of the graph" in {
      val graphEdges = Map.empty[C,Set[C]] ++ ISZ(('A', Set.empty ++ ISZ('B', 'D')),('B', Set.empty ++ ISZ('E')), ('C', Set.empty ++ ISZ('F')),
      ('D', Set.empty ++ ISZ('E', 'F')), ('E', Set.empty ++ ISZ('H', 'G')), ('F', Set.empty ++ ISZ('G', 'I')),
      ('G', Set.empty ++ ISZ('J', 'I')), ('H', Set.empty ++ ISZ('J')))
      val g = new TarjanGraphMapsAsEdges[C](graphEdges)
      assert(!g.hasCycle)
      val expectedOrder = ISZ[C]('C', 'A', 'D', 'F', 'B', 'E', 'G', 'I', 'H', 'J')
      val order = g.topologicalSort(graphEdges)
      println(order)
      assert(order == expectedOrder)
      //This in from the post-condition of the function for doing the topological sorting
      assert(All(order.indices)(n => !Exists(order.indices)(j => j > n && g.inLoop(order(j), order(n), graphEdges))))
    }


}