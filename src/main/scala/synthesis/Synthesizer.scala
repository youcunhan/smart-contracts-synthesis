package synthesis

import datalog.Program
import verification.{TransitionSystem, Verifier}
import synthesis.StateMachine

case class Synthesizer() {

  def synthesize(name: String): Program = {
    val temporalProperties: TemporalProperty = TemporalProperty()
    val filepath = "./synthesis-benchmark/" + name + "/" + name + ".dl"

    val dl = parseProgram(filepath)
    stateMachine.readFromProgram(dl)
    /** The CEGIS loop.  */
    stateMachine.cegis()
  }
}
