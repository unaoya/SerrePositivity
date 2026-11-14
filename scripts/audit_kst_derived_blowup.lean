import SerrePositivity.KST.DerivedBlowup
import Lean.Util.CollectAxioms

/-!
概要：K-L5 の導来 blowup モジュールの全定数を公理監査する。
方針：生成宣言もモジュール名で抽出し依存を再帰検査する。
規約：propext・Classical.choice・Quot.sound 以外は拒否する。
使われ方：KST §3 の各保存単位の対象ビルド後に実行する。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless ((`SerrePositivity.KST.DerivedBlowup).isPrefixOf mod || mod == `SerrePositivity.CommutativeAlgebra.Module.ScalarTensorView) do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-L5: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "K-L5: no declarations audited"
  logInfo m!"K-L5 audit passed: {count} declarations, standard three axioms only."
