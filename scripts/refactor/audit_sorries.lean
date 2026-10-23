import SerrePositivity
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets : Array Name := #[`SerrePositivity.Inputs.Homotopy.kanQuillen_model_exists,
    `SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3,
    `SerrePositivity.theorem_3_1_K0, `SerrePositivity.Section4.supportedRankK0_descent]
  let mut visited : NameSet := {}
  let mut stack : List Name := [`SerrePositivity.main_statement]
  let mut sorried : Array Name := #[]
  let mut count : Nat := 0
  while h : stack ≠ [] do
    let n := stack.head h
    stack := stack.tail
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => continue
    | some ci =>
      count := count + 1
      let used := ci.getUsedConstantsAsSet
      if used.contains ``sorryAx then
        match ci.value? with
        | some v => if (v.getUsedConstants).contains ``sorryAx then sorried := sorried.push n
        | none => pure ()
      for c in used.toList do
        if !visited.contains c then stack := c :: stack
  logInfo m!"visited {count} constants"
  logInfo m!"declarations with a direct sorry in the closure of main_statement: {sorried}"
  for t in targets do
    logInfo m!"{t} in environment: {(env.find? t).isSome}, in closure: {visited.contains t}"
