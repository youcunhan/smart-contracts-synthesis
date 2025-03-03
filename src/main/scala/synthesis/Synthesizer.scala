package synthesis

import datalog.Program
import verification.{TransitionSystem, Verifier}
import synthesis.StateMachine

case class Synthesizer(dl: Program, example_traces: Set[ExampleTrace],
                       temporalProperties: Set[TemporalProperty]) {

  def go(): Program = {
    temporalProperties
    /** Translate dl into a transition system. */
    val statemachine: StateMachine = StateMachine()
    stateMachine.readFromProgram(dl)
    /** The CEGIS loop.  */
    stateMachine.cegis()
  }
}
