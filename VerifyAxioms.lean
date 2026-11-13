import Mogulskii
import Lean.Util.CollectAxioms

#print axioms Mogulskii.pathLargeDeviation
#print axioms Mogulskii.smallDeviationStatement
#print axioms Mogulskii.smallDeviation_log_tendsto

open Lean in
run_cmd do
  for theoremName in [``Mogulskii.pathLargeDeviation, ``Mogulskii.smallDeviationStatement,
      ``Mogulskii.smallDeviation_log_tendsto] do
    let unexpected := (← collectAxioms theoremName).filter fun axiomName =>
      axiomName != ``propext && axiomName != ``Classical.choice && axiomName != ``Quot.sound
    unless unexpected.isEmpty do
      throwError m!"'{theoremName}' depends on unexpected axioms: {unexpected.toList}"
