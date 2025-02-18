package synthesis

import z3.scala._
import verification.TransitionSystem

class SmartContractStateMachine(name: String, ctx: Context) {
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

  val (now, nowOut): (Expr[BitVecSort], Expr[BitVecSort]) = addState("now", ctx.mkBitVecSort(256))
  val (func, funcOut): (Expr[StringSort], Expr[StringSort]) = addState("func", ctx.mkStringSort())

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
    val newTransferFunc = Z3.And(transferFunc, Z3.Eq(funcOut, ctx.mkString(trName)), Z3.Eq(once(trName)._2, ctx.mkBool(true)))

    states.foreach { case (stateName, (state, _)) =>
      if (stateName != "now" && stateName != "func") {
        transferFunc = Z3.simplify(Z3.And(newTransferFunc, Z3.Eq(prev(state)._2, state)))
        if (!contains(states(stateName)._2, transferFunc)) {
          transferFunc = Z3.simplify(Z3.And(transferFunc, Z3.Eq(states(stateName)._2, state)))
        }
      }
    }
    transferFunc(trName) = transferFunc
  }

  def addOnce(): Unit = {
    transitions.foreach { tr =>
      once.foreach { case (onceName, onceVal) =>
        if (onceName != tr) {
          transferFunc(tr) = Z3.And(transferFunc(tr), Z3.Eq(onceVal._2, onceVal._1))
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
      conditionGuards(trName) = Z3.simplify(Z3.And(newGuards: _*))
      true
    }
  }

  def addGuard(trName: String, newGuards: Expr[BoolSort]*): Boolean = {
    if (!transitions.contains(trName)) {
      println("Transition not found!")
      false
    } else {
      conditionGuards(trName) = Z3.simplify(Z3.And(conditionGuards(trName), newGuards: _*))
      true
    }
  }

  def setInit(initState: Expr[BoolSort]): Unit = {
    ts.setInit(Z3.And(initState, Z3.Eq(now, ctx.mkInt(0)), Z3.Eq(func, ctx.mkString("init"))))
    once.values.foreach { case (onceVar, _) =>
      ts.setInit(Z3.simplify(Z3.And(ts.getInit(), Z3.Eq(onceVar, ctx.mkBool(false)))))
    }
  }
}