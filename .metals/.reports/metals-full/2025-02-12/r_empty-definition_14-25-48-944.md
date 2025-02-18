error id: synthesis/
file://<WORKSPACE>/src/main/scala/synthesis/BoundedModelChecking.scala
empty definition using pc, found symbol in pc: synthesis/
semanticdb not found
|empty definition using fallback
non-local guesses:
	 -

Document text:

```scala
package synthesis

import com.microsoft.z3._

object BoundedModelChecking {

  var index = 0
  def fresh(s: Sort, ctx: Context): Expr = {
    index += 1
    ctx.mkConst(s"!f$index", s)
  }

  def zipp[T, U](xs: List[T], ys: List[U]): List[(T, U)] = {
    xs.zip(ys)
  }

  def bmc(init: BoolExpr, trans: BoolExpr, goal: BoolExpr, fvs: List[Expr], xs: List[Expr], xns: List[Expr], ctx: Context): Unit = {
    val solver = ctx.mkSolver()
    solver.add(init)
    var count = 0

    while (true) {
      println(s"iteration $count")
      count += 1

      val p = fresh(ctx.mkBoolSort(), ctx)
      solver.add(ctx.mkImplies(p.asInstanceOf[BoolExpr], goal))

      if (solver.check() == Status.SATISFIABLE) {
        println(s"Model: ${solver.getModel}")
        return
      }

      solver.add(trans)
      val ys = xs.map(x => fresh(x.getSort, ctx))
      val nfvs = fvs.map(x => fresh(x.getSort, ctx))

      val newTrans = substitute(trans, zipp(xns ++ xs ++ fvs, ys ++ xns ++ nfvs))
      val newGoal = substitute(goal, zipp(xs, xns))

      bmc(init, newTrans, newGoal, nfvs, ys, xns, ctx)
    }
  }

  def substitute(expr: Expr, bindings: List[(Expr, Expr)]): Expr = {
    var result = expr
    for ((oldExpr, newExpr) <- bindings) {
      result = result.substitute(oldExpr, newExpr)
    }
    result
  }

  def testbmc(): Unit = {
    val ctx = new Context()

    val x0 = ctx.mkConst("x0", ctx.mkBitVecSort(4))
    val x1 = ctx.mkConst("x1", ctx.mkBitVecSort(4))

    val init = ctx.mkEq(x0, ctx.mkInt(0, 4))        // x0 == 0
    val trans = ctx.mkEq(x1, ctx.mkAdd(x0, ctx.mkInt(3, 4)))  // x1 == x0 + 3
    val goal = ctx.mkEq(x0, ctx.mkInt(10, 4))        // x0 == 10

    bmc(init, trans, goal, List(), List(x0), List(x1), ctx)
  }
}

```

#### Short summary: 

empty definition using pc, found symbol in pc: synthesis/