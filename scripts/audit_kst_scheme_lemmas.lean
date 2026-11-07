import SerrePositivity.AlgebraicGeometry
import Lean.Util.CollectAxioms

/-!
概要：代数幾何の補題と移動前の互換 alias を公理監査する。
方針：宣言元モジュールで抽出し、生成宣言も含め依存を再帰的に調べる。
規約：標準三公理 propext・Classical.choice・Quot.sound だけを許す。
使われ方：各保存単位をビルドした後 `lake env lean` で実行する。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.AlgebraicGeometry |>.isPrefixOf mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "AlgebraicGeometry: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "AlgebraicGeometry: no declarations audited"
  logInfo m!"AlgebraicGeometry audit passed: {count} declarations, standard three axioms only."
