import SerrePositivity.InfinityCategories.Project.Entrypoints.NativeTriangleSupplyAll
import Lean.Util.CollectAxioms

/-!
概要：S-1 の二単体供給の私有補題を含む全宣言を監査する。
方針：定義元モジュールで選別する。
規約：標準三公理のみ。使われ方：独自集約の検証。
-/
open Lean in
run_cmd do
  let env ← getEnv
  let owned := #[`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativeExt]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless owned.contains env.header.modules[idx.toNat]!.module do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "S-1: ModelCategory assumption in {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "S-1: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "S-1: no declarations audited"
  logInfo m!"S-1 triangle: {count} declarations audited; standard axioms only."

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
universe u v

-- 依頼された型をそのまま照合する。
example : ∀ (C : Type v) [Category.{u} C] [SimplicialCategory C]
    (F G : (SimplicialNerve C) _⦋2⦌),
    (SimplicialNerve C).δ (0 : Fin 3) F = (SimplicialNerve C).δ (0 : Fin 3) G →
    (SimplicialNerve C).δ (2 : Fin 3) F = (SimplicialNerve C).δ (2 : Fin 3) G →
    HEq (F.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      (G.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) → F = G := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeTriangle_ext
