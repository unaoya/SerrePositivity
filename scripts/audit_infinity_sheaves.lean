import SerrePositivity.InfinityCategories.Project.Entrypoints.InfinitySheaves
import Lean.Util.CollectAxioms

/-!
# 監査：∞ 層の一般論（5∞-1）の入口のモジュール

入口 `Entrypoints.InfinitySheaves` が直接 import するモジュールの全宣言について、使う公理が
propext・Classical.choice・Quot.sound だけであることを確かめる（2026-11-18 の取り込みで新設）。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `SerrePositivity.InfinityCategories.Project.Entrypoints.InfinitySheaves
    | throwError "InfinitySheaves: entry point not found"
  let owned : Std.HashSet Name := Std.HashSet.ofArray
    (env.header.moduleData[idx.toNat]!.imports.map (·.module))
  let mut count : Nat := 0
  for (name, _) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? name | continue
    unless owned.contains env.header.modules[i.toNat]!.module do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "InfinitySheaves: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "InfinitySheaves: no declarations audited"
  logInfo m!"InfinitySheaves audit passed: {count} declarations in {owned.size} modules, standard three axioms only."
