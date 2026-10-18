import SerrePositivity.KST.Descent
import Lean.Util.CollectAxioms

/-!
## 概要
K-L8 の全宣言を内部補助宣言も含めて監査する。
## 方針
定数の定義元モジュールで選び、再帰的な依存公理を検査する。
## 規約
許容する公理は標準三公理だけ。公理の監査と数学的工程の完成は別に判定する。
## 使われ方
各保存単位で `lake env lean scripts/audit_kst_descent.lean` を実行する。
-/

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.Descent).isPrefixOf mod do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax ↦
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do throwError "Unexpected axioms in {name}: {unexpected}"
    declarations := declarations + 1
    unless modules.contains mod do modules := modules.push mod
  for expected in #[`SerrePositivity.KST.Descent.Axioms,
      `SerrePositivity.KST.Descent.Transfer,
      `SerrePositivity.KST.Descent.RationalFixedPoints,
      `SerrePositivity.KST.Descent.PiComparison,
      `SerrePositivity.KST.Descent.DiagramTransfer,
      `SerrePositivity.KST.Descent.InvariantExactness,
      `SerrePositivity.KST.Descent.PresheafAction,
      `SerrePositivity.KST.Descent.InvariantsHomology,
      `SerrePositivity.KST.Descent.SplitCech,
      `SerrePositivity.KST.Descent.NilpotentThickening,
      `SerrePositivity.KST.Descent.SchemeFacts,
      `SerrePositivity.KST.Descent.ClosedDimension,
      `SerrePositivity.KST.Descent.BlowupGeometry,
      `SerrePositivity.KST.Descent.MayerVietoris,
      `SerrePositivity.KST.Descent.SquareSequence,
      `SerrePositivity.KST.Descent.CoincidenceLocus,
      `SerrePositivity.KST.Descent.EquivariantMayerVietoris,
      `SerrePositivity.KST.Descent.PermutationRepresentation,
      `SerrePositivity.KST.Descent.InvariantProducts,
      `SerrePositivity.KST.Descent.SplitMayerVietoris,
      `SerrePositivity.KST.Descent.Theorem31,
      `SerrePositivity.KST.Descent.ReducedClosedSubscheme,
      `SerrePositivity.KST.Descent.CoincidenceCenter,
      `SerrePositivity.KST.Descent.ClosedCenterSquare,
      `SerrePositivity.KST.Descent.AffineReduction,
      `SerrePositivity.KST.Descent.ReductionFunctor,
      `SerrePositivity.KST.Descent.NoetherianReduction,
      `SerrePositivity.KST.Descent.FiniteTypeReduction,
      `SerrePositivity.KST.Descent.DescentNaturality,
      `SerrePositivity.KST.Descent.ReductionDescent,
      `SerrePositivity.KST.Descent.FiniteCoproduct,
      `SerrePositivity.KST.Descent.SectionOrbit,
      `SerrePositivity.KST.Descent.ClosedCoproduct,
      `SerrePositivity.KST.Descent.SectionCoincidence,
      `SerrePositivity.KST.Descent.CoproductRestriction,
      `SerrePositivity.KST.Descent.ClosedImmersionSquare,
      `SerrePositivity.KST.Descent.OrbitGeometry] do
    unless modules.contains expected do throwError "Required module missing: {expected}"
  logInfo m!"KST descent audit passed: {declarations} declarations in {modules.size} modules."
  logInfo "Standard axioms only. This checks dependencies, not completion of Theorem 3.1."
