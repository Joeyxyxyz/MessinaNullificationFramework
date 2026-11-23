import Lean
import MNFCore.Operator
import MNFCore.Bits
import MNFCore.WState
import MNFCore.GHZ
import MNFCore.Hadamard
import MNFCore.Decay
import MNFCore.Conservation
open Lean Elab Command in
elab "#audit_all" : command => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if n.getRoot == `MNF then
      match ci with
      | .thmInfo _ => names := names.push n
      | _ => pure ()
  for n in names.qsort (fun a b => a.toString < b.toString) do
    let s ← liftCoreM (Lean.collectAxioms n)
    logInfo m!"{n} : {s.toList}"
#audit_all
