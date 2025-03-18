package synthesis

import datalog.Program
import verification.{TransitionSystem, Verifier}
import synthesis.StateMachine
import synthesis.Parser

case class Synthesizer() {

  def synthesize(name: String) = {
    val temporalProperties: TemporalProperty = TemporalProperty()
    val datalogpath = "./synthesis-benchmark/" + name + "/" + name + ".dl"
    val propertypath = "./synthesis-benchmark/" + name + "/temporal_properties.txt"
    val tracepath = "./synthesis-benchmark/" + name + "/example_traces.txt"

    val dl = parseProgram(datalogpath)
    stateMachine.readFromProgram(dl)
    /** The CEGIS loop.  */
    val property = Parser.parseProperty(propertypath)
    val postrace = Parser.parseTrace(tracepath)
    statemachine.addOnce()
    statemachine.generate_candidate_guards()
    stateMachine.cegis(property, postrace)
  }
}
