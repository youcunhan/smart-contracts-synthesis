package synthesis

import com.microsoft.z3._
import verification.TransitionSystem

class StateMachine(name: String, ctx: Context) {
  val states: scala.collection.mutable.Map[String, (Expr[_], Expr[_])] = scala.collection.mutable.Map()
  val prevStates: scala.collection.mutable.Map[String, (Expr[_], Expr[_])] = scala.collection.mutable.Map()
  val once: scala.collection.mutable.Map[String, (Expr[_], Expr[_])] = scala.collection.mutable.Map()
  var transitions: List[String] = List()
  val conditionGuards: scala.collection.mutable.Map[String, Expr[BoolSort]] = scala.collection.mutable.Map()
  val candidateConditionGuards: scala.collection.mutable.Map[String, List[Expr[BoolSort]]] = scala.collection.mutable.Map()
  val trParameters: scala.collection.mutable.Map[String, List[Expr[_]]] = scala.collection.mutable.Map()
  val transferFunc: scala.collection.mutable.Map[String, Expr[BoolSort]] = scala.collection.mutable.Map()
  val constants: List[String] = List()
  val ts: TransitionSystem = new TransitionSystem(name, ctx)
  var nowState: Option[String] = None

  val (now, nowOut): (Expr[BitVecSort], Expr[BitVecSort]) = addState("now", ctx.mkBitVecSort(256)).asInstanceOf[(Expr[BitVecSort], Expr[BitVecSort])]
  val (func, funcOut): (Expr[_], Expr[_]) = addState("func", ctx.mkStringSort())

  def addState(stateName: String, stateType: Sort): (Expr[_], Expr[_]) = {
    val (state, stateOut) = ts.newVar(stateName, stateType)
    val (prevState, prevStateOut) = ts.newVar(s"prev_$stateName", stateType)
    if (stateName != "func" && !stateName.startsWith("once_")) {
      states(stateName) = (state, stateOut)
      prevStates(stateName) = (prevState, prevStateOut)
    }
    (state, stateOut)
  }

  def prev(state: Expr[_]): (Expr[_], Expr[_]) = {
    prevStates(state.toString)
  }

  def addTr(trName: String, parameters: List[Expr[_]], guard: Expr[BoolSort], transferFunc: Expr[BoolSort]): Unit = {
    transitions = transitions :+ trName
    once(trName) = addState(s"once_$trName", ctx.mkBoolSort())
    trParameters(trName) = parameters
    conditionGuards(trName) = guard
    candidateConditionGuards(trName) = List()
    val newTransferFunc = ctx.mkAnd(transferFunc, ctx.mkEq(funcOut, ctx.mkString(trName)), ctx.mkEq(once(trName)._2, ctx.mkBool(true)))

    states.foreach { case (stateName, (state, _)) =>
      if (stateName != "now" && stateName != "func") {
        transferFunc = z3.simplify(ctx.mkAnd(newTransferFunc, ctx.mkEq(prev(state)._2, state)))
        if (!contains(states(stateName)._2, transferFunc)) {
          transferFunc = z3.simplify(ctx.mkAnd(transferFunc, ctx.mkEq(states(stateName)._2, state)))
        }
      }
    }
    transferFunc(trName) = transferFunc
  }

  def addOnce(): Unit = {
    transitions.foreach { tr =>
      once.foreach { case (onceName, onceVal) =>
        if (onceName != tr) {
          transferFunc(tr) = ctx.mkAnd(transferFunc(tr), ctx.mkEq(onceVal._2, onceVal._1))
        }
      }
    }
  }

  def clearGuards(): Unit = {
    conditionGuards.keys.foreach { key =>
      conditionGuards(key) = ctx.mkBool(true)
    }
  }

  def changeGuard(trName: String, newGuards: Expr[BoolSort]*): Boolean = {
    if (!transitions.contains(trName)) {
      println("Transition not found!")
      false
    } else {
      conditionGuards(trName) = z3.simplify(ctx.mkAnd(newGuards: _*))
      true
    }
  }

  def addGuard(trName: String, newGuards: Expr[BoolSort]*): Boolean = {
    if (!transitions.contains(trName)) {
      println("Transition not found!")
      false
    } else {
      conditionGuards(trName) = z3.simplify(ctx.mkAnd(conditionGuards(trName), newGuards: _*))
      true
    }
  }

  def setInit(initState: Expr[BoolSort]): Unit = {
    ts.setInit(ctx.mkAnd(initState, ctx.mkEq(now, ctx.mkInt(0)), ctx.mkEq(func, ctx.mkString("init"))))
    once.values.foreach { case (onceVar, _) =>
      ts.setInit(z3.simplify(ctx.mkAnd(ts.getInit(), ctx.mkEq(onceVar, ctx.mkBool(false)))))
    }
  }
  def transfer(tr_name: String, candidates: Map[String, List[Expr[BoolSort]]], next: List[Expr[BoolSort]], parameters: Expr[_]*): Option[List[Expr[BoolSort]]] = {
    val success = ctx.mkAnd(now_state, condition_guards(tr_name), nowOut > now_state, ctx.mkAnd(parameters: _*))
    val s = new Solver()
    s.add(success)
    val result = s.check()

    if (result == Status.Unsat) {
      return None
    } else {
      s.reset()
      s.add(ctx.mkAnd(now_state, transfer_func(tr_name), ctx.mkAnd(parameters: _*)))
      val result2 = s.check()
      val model = s.model()
      now_state = z3.Bool(true)
      states.foreach { case (_, (state, _)) =>
        now_state = ctx.mkAnd(now_state, state == model.eval(state))
      }
      now_state = z3.simplify(now_state)

      s.reset()
      s.add(now_state)
      s.add(next.tail)
      val finalCheck = s.check()

      if (finalCheck == Status.Sat) {
        val m = s.model()
        val newLine = candidates(next.head).map(c => m.eval(c))
        Some(newLine)
      } else {
        println("error")
        None
      }
    }
  }

  def simulate(trace: List[List[Expr[BoolSort]]], candidates: Map[String, List[Expr[BoolSort]]]): List[List[Expr[BoolSort]]] = {
    var res: List[List[Expr[BoolSort]]] = List()
    now_state = ts.getInit()

    val s = new Solver()
    s.add(now_state)
    s.add(trace.head.tail)
    if (s.check() == Status.Sat) {
      val m = s.model()
      val newline = candidates(trace.head.head).map(c => m.eval(c))
      res = List(newline)
    }

    for (i <- 0 until trace.size - 1) {
      val tr_name = trace(i).head.toString
      var newline = List(tr_name) ++ res.head
      res = res :+ newline
      val nextLine = transfer(tr_name, candidates, trace(i + 1), trace(i).tail: _*)
      if (nextLine.isEmpty) {
        return res
      }
      res = res :+ nextLine.get
    }
    res
  }

  def bmc(property: Expr[BoolSort]): Option[List[List[Expr[BoolSort]]]] = {
    import lib.bmc._
    lib.bmc.index = 0
    ts.setTr(z3.Bool(false), Set())

    transitions.foreach { tr =>
      ts.setTr(z3.simplify(z3.Or(ts.getTr(), ctx.mkAnd(transfer_func(tr), condition_guards(tr), nowOut > now_state))))
    }

    val xs = states.values.map(_._1) ++ states.values.map(_._2) ++ List(nowOut)
    val xns = states.values.map(_._2) ++ List(nowOut)

    val model = bmc(ts.getInit(), ts.getTr(), property, xs, xns)
    model match {
      case Some(m) =>
        val trace = (1 until m.size - 2).map { i =>
          val tr = m(i)("func").toString
          val rule = List(tr, nowOut == m(i)("now"))
          rule
        }.toList
        Some(trace)
      case None =>
        println("No model found!")
        None
    }
  }

  def generate_candidate_guards(predicates: List[String], array: Boolean): Map[String, List[Expr[BoolSort]]] = {
    var candidateGuards: Map[String, List[Expr[BoolSort]]] = Map()
    transitions.foreach { tr =>
      candidateGuards += tr -> List()

      val s = constants ++ states.values.map(_._1) ++ tr_parameters.getOrElse(tr, List()) ++ List(nowOut)
      if (array) {
        val arrayEnum = s.collect { case arr if z3.isArray(arr) => arr }
        candidateGuards(tr) ++= arrayEnum
      }

      s.zipWithIndex.foreach { case (ls, lsIdx) =>
        if (z3.isBool(ls)) {
          candidateGuards(tr) ++= List(ls, z3.Not(ls))
        }
        s.zipWithIndex.drop(lsIdx + 1).foreach { case (rs, rsIdx) =>
          if (!(z3.isArray(ls) || z3.isArray(rs) || z3.isBool(rs))) {
            predicates.foreach { predicate =>
              try {
                val guard = predicate match {
                  case "<"  => ls < rs
                  case "<=" => ls <= rs
                  case ">"  => ls > rs
                  case ">=" => ls >= rs
                  case "="  => ls == rs
                  case _    => throw new IllegalArgumentException("Unsupported predicate")
                }
                candidateGuards(tr) :+= guard
              } catch {
                case _: Exception => println("Predicate mismatch")
              }
            }
          }
        }
      }
    }
    candidateGuards
  }

  def synthesize(pos: List[List[List[Expr[BoolSort]]]], neg: List[List[List[Expr[BoolSort]]]], candidates: Map[String, List[Expr[BoolSort]]]): Unit = {
    val s = new Solver()
    var approvePos = z3.Bool(true)
    pos.foreach { postrace =>
      var approveT = z3.Bool(true)
      postrace.foreach { trRes =>
        val tr = trRes.head
        var approvetx = z3.Bool(true)
        trRes.tail.foreach { res =>
          approvetx = ctx.mkAnd(approvetx, z3.Implies(candidate_condition_guards(tr).head, res))
        }
        approveT = ctx.mkAnd(approveT, approvetx)
      }
      approvePos = ctx.mkAnd(approvePos, approveT)
    }

    var approveNeg = z3.Bool(true)
    neg.foreach { negtrace =>
      var approveT = z3.Bool(true)
      negtrace.foreach { trRes =>
        val tr = trRes.head
        var approvetx = z3.Bool(true)
        trRes.tail.foreach { res =>
          approvetx = ctx.mkAnd(approvetx, z3.Implies(candidate_condition_guards(tr).head, res))
        }
        approveT = ctx.mkAnd(approveT, approvetx)
      }
      approveNeg = ctx.mkAnd(approveNeg, z3.Not(approveT))
    }

    s.add(approvePos)
    s.add(approveNeg)
    val result = s.check()
    if (result == Status.Sat) {
      val model = s.model()
      transitions.foreach { tr =>
        candidates(tr).foreach { c =>
          if (model.eval(candidate_condition_guards(tr).head).asBool) {
            addGuard(tr, c)
          }
        }
      }
    } else {
      println("No solution found!")
    }
  }

  def cegis(properties: List[Expr[BoolSort]], positive_traces: List[List[List[Expr[BoolSort]]]], candidate_guard: Map[String, List[Expr[BoolSort]]], array: Boolean = true): Unit = {
    var pos = List[List[List[Expr[BoolSort]]]]()
    var neg = List[List[List[Expr[BoolSort]]]]()

    positive_traces.foreach { trace =>
      pos :+= simulate(trace, candidate_guard)
    }

    var iter = 0
    while (true) {
      iter += 1
      synthesize(pos, neg, candidate_guard)

      var new_ntraces = List[List[List[Expr[BoolSort]]]]()
      properties.foreach { p =>
        val ntrace = bmc(z3.Not(p))
        if (ntrace.isEmpty) {
          println("√") // Property verified
        } else {
          new_ntraces = new_ntraces :+ ntrace.get
          println("×") // Property not verified
        }
      }

      if (new_ntraces.isEmpty) {
        println("All properties verified!")
        break
      }

      // Update negative traces
      new_ntraces.foreach { negtrace =>
        neg :+= simulate(negtrace, candidate_guard)
      }
    }
  }


  def readFromProgram(p: Program): List[List[List[Expr[BoolSort]]]] = {
    val materializedRelations: Set[Relation] = Set()
    val impTranslator = new ImperativeTranslator(dl, materializedRelations, isInstrument=true, enableProjection=true,
      monitorViolations = false, arithmeticOptimization = true)
    val imperative = impTranslator.translate()
    // println(imperative)
    val verifier = new Verifier(dl, imperative)
    verifier.check()
    val statemachine: StateMachine = StateMachine()
  }
  

}