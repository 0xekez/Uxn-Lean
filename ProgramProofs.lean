import ProgramProofs.Fibonacci
import ProgramProofs.HelloWorld
import ProgramProofs.HelloWorld.Refinement
import ProgramProofs.Sierpinski
import ProgramProofs.Uxnmin.Correctness
import ProgramProofs.Uxnmin.RankedSimulation

-- Only the standard logical axioms are permitted. This also rejects unfinished
-- proofs and any generated native-evaluation axiom, including transitive uses.
run_cmd do
  for name in [``ProgramProofs.Fibonacci.correct,
      ``ProgramProofs.HelloWorld.correct,
      ``ProgramProofs.HelloWorld.refinement_conditions,
      ``ProgramProofs.HelloWorld.refinement_conditions_file,
      ``ProgramProofs.HelloWorld.refines,
      ``ProgramProofs.HelloWorld.hello_world_refinement_conditions,
      ``ProgramProofs.Sierpinski.correct,
      ``ProgramProofs.RankedSimulation.preserves,
      ``ProgramProofs.Uxnmin.correct,
      ``ProgramProofs.Uxnmin.correct_file] do
    for axiomName in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name} depends on unexpected axiom {axiomName}"
