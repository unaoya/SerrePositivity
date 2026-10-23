module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoBoundaryHomComparison

/-!
概要：実際の二次元境界比較の面・ホーンへの制限は、同じ補正比較そのもの。
方針：両側の表示同型の射影と、同じ厳密 pullback 比較の両射影を計算する。
規約：元の境界の直接制限を保持する。
使われ方：元の大域 Hom 作用との指定同型を貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "N" => cocartesianPullbackNativeLiftCoreFunctor p.val.hom q.val.hom
local notation "T" => intervalDiagramLiftOverFunctor
  (cocartesianStrictTransportCoherentDiagram p.val.hom)
  (cocartesianStrictTransportCoherentDiagram q.val.hom)

/-- 同じ実際の境界比較の面側制限は、元の直接制限と同じ補正面比較。 -/
lemma cocartesianTwoBoundaryHomComparison_face :
    cocartesianTwoBoundaryHomComparison j p q ≫
      (T).map (HornBoundaryOver.faceInclusion 1 1 σ).op =
    (N).map (HornBoundaryOver.faceInclusion 1 1 σ).op ≫
      cocartesianTwoBoundaryFaceComparison j p q := by
  rw [← cocartesianTwoBoundaryTargetPresentationIso_hom_fst, ← Category.assoc,
    cocartesianTwoBoundaryHomComparison_presentation, Category.assoc,
    cocartesianTwoBoundaryPullbackComparison_fst, ← Category.assoc,
    cocartesianTwoBoundaryNativePresentationIso_hom_fst]

/-- 同じ実際の境界比較のホーン側制限も、元の直接制限と同じ補正ホーン比較。 -/
lemma cocartesianTwoBoundaryHomComparison_horn :
    cocartesianTwoBoundaryHomComparison j p q ≫
      (T).map (HornBoundaryOver.hornInclusion 1 1 σ).op =
    (N).map (HornBoundaryOver.hornInclusion 1 1 σ).op ≫
      cocartesianTwoBoundaryHornComparison j p q := by
  rw [← cocartesianTwoBoundaryTargetPresentationIso_hom_snd, ← Category.assoc,
    cocartesianTwoBoundaryHomComparison_presentation, Category.assoc,
    cocartesianTwoBoundaryPullbackComparison_snd, ← Category.assoc,
    cocartesianTwoBoundaryNativePresentationIso_hom_snd]

end SerrePositivity.InfinityCategories
