import com.microsoft.z3._
import scala.io.Source
import scala.util.matching.Regex

object Parser {

  val ctx = new Context()

  def parseProperty(path: String): Seq[BoolExpr] = {
    val lines = Source.fromFile(path).getLines().filter(_.nonEmpty).filterNot(_.startsWith("//")).toSeq
    lines.map(parseLogicalExpr)
  }

  def parseTrace(path: String): Seq[Expr] = {
    val lines = Source.fromFile(path).getLines()
      .filter(_.nonEmpty)
      .filterNot(_.startsWith("//"))
      .toSeq

    lines.map(parseAction)
  }

  private def parseLogicalExpr(line: String): BoolExpr = {
    // Replace symbols with Z3 equivalents
    val z3line = line
      .replace("□", "forall t, ")
      .replace("♦", "exists t, ")
      .replace("∧", "&&")
      .replace("∨", "||")
      .replace("¬", "!")
      .replace("→", "=>")

    ctx.parseSMTLIB2String(s"(assert $z3line)", null, null, null, null).head.asInstanceOf[BoolExpr]
  }

  private def parseAction(line: String): Expr = {
    val actionPattern: Regex = "(\\w+)\\((.*?)\\)@(\\d+);".r

    line match {
      case actionPattern(name, args, timestamp) =>
        val argExprs = args.split(",").map(_.trim.split("=")).map {
          case Array(key, value) => ctx.mkEq(ctx.mkConst(key, ctx.mkIntSort()), parseValue(value))
        }

        ctx.mkApp(ctx.mkFuncDecl(name, argExprs.map(_ => ctx.mkBoolSort()), ctx.mkBoolSort()), argExprs: _*)

      case _ => throw new RuntimeException(s"Invalid action format: $line")
    }
  }

  private def parseValue(v: String): Expr = {
    if (v.startsWith("0x"))
      ctx.mkBV(Integer.parseInt(v.substring(2), 16), 256)
    else
      ctx.mkInt(v.toInt)
  }
}
