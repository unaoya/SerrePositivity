import SerrePositivity.EInfinity
import Lean.Util.CollectAxioms

-- EInfinity の全宣言の推移的な公理依存を監査する。
open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.EInfinity).isPrefixOf mod do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax ↦
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "非標準公理への依存: {name}: {unexpected}"
    declarations := declarations + 1
  if declarations == 0 then throwError "監査対象の EInfinity 宣言がありません"
  unless env.contains `SerrePositivity.EInfinity.projectiveModelCategory do
    throwError "射影モデル構造の宣言がありません"
  for required in #[`SerrePositivity.EInfinity.BarrattEccles.operad,
      `SerrePositivity.EInfinity.BarrattEccles.augmentation,
      `SerrePositivity.EInfinity.BarrattEccles.augmentation_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.complexContraction,
      `SerrePositivity.EInfinity.BarrattEccles.equivariantBasis_rightAction,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonalDegree_eq_sum,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_projection,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_natural,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_coassoc,
      `SerrePositivity.EInfinity.AlexanderWhitney.counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_left_counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_right_counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.counit_natural] do
    unless env.contains required do
      throwError "EInfinity の必要な宣言がありません: {required}"
  logInfo m!"EInfinity 公理監査成功: {declarations} 宣言。標準 3 公理のみ。"
