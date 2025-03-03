package synthesis

import com.microsoft.z3.{BoolExpr, BoolSort, Context, Expr, Solver, Sort, Status}

object BoundedModelChecking {
  private var index: Int = 0

  def pureName(name: String): String = {
    if (name.contains("|")) name.substring(0, name.indexOf('|')) else name
  }

  def fresh(round: Int, ctx: Context, name: String, sort: Sort): Expr[_] = {
    index += 1
    ctx.mkConst(s"${name}|r${round}|i${index}", sort)
  }

  def zipp(xs: Array[Expr[_]], ys: Array[Expr[_]]): Array[(Expr[_], Expr[_])] = {
    xs.zip(ys)
  }

  def bmc(ctx: Context, init: BoolExpr, trans: BoolExpr, goal: BoolExpr,
          fvs: Array[Expr[_]], xs: Array[Expr[_]], xns: Array[Expr[_]]): Option[Map[String, Expr[_]]] = {
    val solver = ctx.mkSolver()
    // solver.reset("timeout", 2000)
    solver.add(init)
    
    var count = 0
    var currentTrans = trans
    var currentGoal = goal
    var currentXs = xs
    var currentXns = xns
    var currentFvs = fvs

    while (count <= 7) {
      count += 1
      val p = fresh(count, ctx, "P", ctx.getBoolSort).asInstanceOf[BoolExpr]
      solver.add(ctx.mkImplies(p, currentGoal))

      val res = solver.check(p)
      if (res == Status.SATISFIABLE) {
        return Some(extractModel(solver.getModel))
      }
      solver.add(currentTrans)

      val ys = currentXs.map(x => fresh(count, ctx, pureName(x.toString), x.getSort))
      val nfvs = currentFvs.map(f => fresh(count, ctx, pureName(f.toString), f.getSort))

      currentTrans = currentTrans.substitute(
        zipp(currentXns ++ currentXs ++ currentFvs, ys ++ currentXns ++ nfvs): _*
      ).asInstanceOf[BoolExpr]
      
      currentGoal = currentGoal.substitute(zipp(currentXs, currentXns): _*).asInstanceOf[BoolExpr]
      
      currentXs = currentXns
      currentXns = ys
      currentFvs = nfvs
    }
    None
  }

  def extractModel(model: com.microsoft.z3.Model): Map[String, Expr[_]] = {
    var extractedModel = Map[String, Expr[_]]()
    val iter = model.getConstDecls.iterator
    
    while (iter.hasNext) {
      val decl = iter.next()
      val name = decl.getName.toString
      val value = model.getConstInterp(decl)
      extractedModel += (pureName(name) -> value)
    }
    extractedModel
  }

  def testbmc(): Unit = {
    val ctx = new Context()
    val bvSize = 8
    val bvSort = ctx.mkBitVecSort(bvSize)
    val x = ctx.mkBVConst("x", bvSize)
    val xn = ctx.mkBVConst("x'", bvSize)
    val init = ctx.mkEq(x, ctx.mkBV(0, bvSize))
    val trans = ctx.mkEq(xn, ctx.mkBVAdd(x, ctx.mkBV(1, bvSize)))
    val goal = ctx.mkEq(x, ctx.mkBV(5, bvSize))
    
    val result = bmc(ctx, init, trans, goal, Array(), Array(x), Array(xn))
    println(result.getOrElse("No model found"))
  }
}
