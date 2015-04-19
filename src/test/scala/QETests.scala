import edu.cmu.cs.ls.keymaera.tactics.Tactics
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tools._
import java.math.BigDecimal
import java.io.File
import scala.collection.immutable._

class QETests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig
  var qet : QETool = null
  val x = Variable("x", None, Real)

  val zero = Number(new BigDecimal("0"))

  def num(n : Integer) = Number(new BigDecimal(n.toString()))
  def snum(n : String) = Number(new BigDecimal(n))

  override def beforeEach() = {
    qet = new JLinkMathematicaLink()
    qet match {
      case qetml : JLinkMathematicaLink => qetml.init(mathematicaConfig("linkName"), None) //@todo jlink
    }
  }

  override def afterEach() = {
    qet match {
      case qetml : JLinkMathematicaLink => qetml.shutdown()
    }
    qet = null
  }

  "Quantifier Eliminator" should "verify that there exists x > 0" in {
    val f = Exists(Seq(x), GreaterThan(Real, x, zero))
    qet.qe(f) should be (True)
  }
}
