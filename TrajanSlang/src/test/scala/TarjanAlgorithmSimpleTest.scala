import org.scalatest.{FlatSpec, Matchers}
import org.sireum._
import org.sireum.ops.ISZOps

import scala.annotation.tailrec

class TarjanAlgorithmSimpleTest extends FlatSpec with Matchers {
  val set1: Set[Z] = Set.empty ++ ISZ(2)
  val set2: Set[Z] = Set.empty ++ ISZ(3)
  val set3: Set[Z] = Set.empty ++ ISZ(4)
  val set4: Set[Z] = Set.empty ++ ISZ(1)
  val edge1: Edge[Z] = Edge(1, set1)
  val edge2: Edge[Z] = Edge(2, set2)
  val edge3: Edge[Z] = Edge(3, set3)
  val edge4: Edge[Z] = Edge(4, set4)
  val allEdges: Set[Edge[Z]] = Set.empty ++ ISZ(edge1, edge2, edge3, edge4)

  @tailrec
  private def generateEdges(n: Z, edges: Set[Edge[Z]] = Set.empty[Edge[Z]]()): Set[Edge[Z]] = {
    if (n == Z(0)) edges
    else generateEdges(n - 1, edges ++ ISZ(Edge(n - 1, Set.empty ++ ISZ(n))))
  }

  "Tarjan " should "report an algebraic loop" in {
    val g = new TarjanGraph[Z](allEdges.elements)
    assert(g.hasCycle)
  }



  "Tarjan Graph with two loops" should "report two algebraic loops" in {
    val edge5: Edge[Z] = Edge(4, Set.empty ++ ISZ(5))
    val edge6: Edge[Z] = Edge(5, Set.empty ++ ISZ(6))
    val edge7: Edge[Z] = Edge(6, Set.empty ++ ISZ(7))
    val edge8: Edge[Z] = Edge(7, Set.empty ++ ISZ(5))

    val edges: Set[Edge[Z]] = allEdges ++ ISZ(edge5, edge6, edge7, edge8)
    val g = new TarjanGraph[Z](edges.elements)
    assert(g.hasCycle)
    assert(g.tarjanCycle.size == 2)
  }

  "Tarjan Graph with three loops" should "report three algebraic loops" in {
    val edge5: Edge[Z] = Edge(4, Set.empty ++ ISZ(5))
    val edge6: Edge[Z] = Edge(5, Set.empty ++ ISZ(6))
    val edge7: Edge[Z] = Edge(6, Set.empty ++ ISZ(7))
    val edge8: Edge[Z] = Edge(6, Set.empty ++ ISZ(5))
    val edge9: Edge[Z] = Edge(8, Set.empty ++ ISZ(7))
    val edge10: Edge[Z] = Edge(7, Set.empty ++ ISZ(8))

    val edges = allEdges ++ ISZ(edge5, edge6, edge7, edge8, edge9, edge10)
    val g = new TarjanGraph[Z](edges.elements)
    assert(g.hasCycle)
    assert(g.tarjanCycle.size == 3)
    //val sort = g.topologicalSort

  }

  "Tarjan BigGrahp 100+ edges" should "report AN algebraic loop" in {
    val alotOfEdges = generateEdges(100) ++ ISZ(Edge(100, Set.empty ++ ISZ(1)))
    val g = new TarjanGraph[Z](alotOfEdges.elements)
    assert(g.hasCycle)
  }

  "Tarjan BigGrahp 1000+ edges" should "report AN algebraic loop" in {
    val alotOfEdges = generateEdges(10000) ++ ISZ(Edge(10000, Set.empty ++ ISZ(1)))
    val g = new TarjanGraph[Z](alotOfEdges.elements)
    assert(g.hasCycle)
  }

  /*
  "Tarjan" should "report NO algebraic loop" in {
    val tests: Iterator[Set[Edge[Z]]] = ISZOps(allEdges.elements)..elements.elements.combinations(3).map(o=> Set.empty[Edge[Z]] ++ ISZ(o))
    assert(tests.forall((f: Set[Edge[Z]]) => {
      val g = new TarjanGraph[Z](f.elements)
      val actual = g.hasCycle
      !actual
    }))
  }*/

  "Tarjan BigGrahp 1000+ edges" should "report NO algebraic loop" in {
    val alotOfEdges = generateEdges(1001)
    val g = new TarjanGraph[Z](alotOfEdges.elements)
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
    val alotOfEdges = generateEdges(100000)
    time {
      val g = new TarjanGraph[Z](alotOfEdges.elements)
      assert(!g.hasCycle)
    }
  }
}