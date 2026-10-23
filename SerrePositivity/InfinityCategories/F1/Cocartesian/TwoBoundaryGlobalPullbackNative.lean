module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoBoundaryGlobalPullbackMaps

/-!
概要：coherent な境界比較を元の大域 Hom 上で面・ホーンへ射影すると、同じ二成分の作用。
方針：実際の境界比較の両射影と元の大域制限の自然性を使う。
規約：元の全 Hom と同じ直接制限を保持する。
使われ方：大域 pullback 同型の二成分を指定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "q₁" => cocartesianTwoBoundaryFaceTargetRestriction p q
local notation "q₂" => cocartesianTwoBoundaryHornTargetRestriction p q
local instance : HasPullback q₁ q₂ :=
  (inferInstance : HasLimitsOfShape WalkingCospan SSet.{u + 1}).has_limit (cospan q₁ q₂)

/-- 同じ大域作用の面側射影は、元の面への制限と同じ補正面比較。 -/
lemma cocartesianTwoBoundaryCorrectedGlobalPullbackMap_fst :
    cocartesianTwoBoundaryCorrectedGlobalPullbackMap j p q ≫ pullback.fst q₁ q₂ =
    cocartesianNativeGlobalDiagramRestriction p.val.hom q.val.hom
      (Over.mk (stdSimplex.δ (1 : Fin 3) ≫ σ)) ≫
        cocartesianTwoBoundaryFaceComparison j p q := by
  rw [cocartesianTwoBoundaryCorrectedGlobalPullbackMap, Category.assoc,
    cocartesianTwoBoundaryTargetPresentationIso_hom_fst, Category.assoc,
    cocartesianTwoBoundaryCoherentHomComparison_face, ← Category.assoc,
    cocartesianNativeGlobalDiagramRestriction_naturality]
  rfl

/-- 同じ大域作用のホーン側射影は、元のホーン制限と同じ coherent な補正比較。 -/
lemma cocartesianTwoBoundaryCorrectedGlobalPullbackMap_snd :
    cocartesianTwoBoundaryCorrectedGlobalPullbackMap j p q ≫ pullback.snd q₁ q₂ =
    cocartesianNativeGlobalDiagramRestriction p.val.hom q.val.hom (cocartesianFiniteHornOver 2 1) ≫
      cocartesianTwoBoundaryCoherentHornComparison j p q := by
  rw [cocartesianTwoBoundaryCorrectedGlobalPullbackMap, Category.assoc,
    cocartesianTwoBoundaryTargetPresentationIso_hom_snd, Category.assoc,
    cocartesianTwoBoundaryCoherentHomComparison_horn, ← Category.assoc,
    cocartesianNativeGlobalDiagramRestriction_naturality]
  rfl

end SerrePositivity.InfinityCategories
