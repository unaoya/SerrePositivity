module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoBoundaryGlobalPullbackNative

/-!
概要：元の分類作用を同じ境界 pullback へ写した両射影は、元の二つの直接制限。
方針：分類先の表示同型の両射影と大域制限の自然性を計算する。
規約：元の分類主写像を保持する。
使われ方：同じ pullback への二つの大域写像を成分同型で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "q₁" => cocartesianTwoBoundaryFaceTargetRestriction p q
local notation "q₂" => cocartesianTwoBoundaryHornTargetRestriction p q
local instance : HasPullback q₁ q₂ :=
  (inferInstance : HasLimitsOfShape WalkingCospan SSet.{u + 1}).has_limit (cospan q₁ q₂)

/-- 元の分類作用の同じ面側射影は、元の面への直接制限。 -/
lemma cocartesianTwoBoundaryOriginalGlobalPullbackMap_fst :
    cocartesianTwoBoundaryOriginalGlobalPullbackMap p q ≫ pullback.fst q₁ q₂ =
    cocartesianStraighteningHomInterval p q ≫ intervalDiagramGlobalDiagramRestriction P Q
      (Over.mk (stdSimplex.δ (1 : Fin 3) ≫ σ)) := by
  rw [cocartesianTwoBoundaryOriginalGlobalPullbackMap, Category.assoc,
    cocartesianTwoBoundaryTargetPresentationIso_hom_fst, Category.assoc,
    intervalDiagramGlobalDiagramRestriction_naturality]
  rfl

/-- 元の分類作用の同じホーン側射影は、元のホーンへの直接制限。 -/
lemma cocartesianTwoBoundaryOriginalGlobalPullbackMap_snd :
    cocartesianTwoBoundaryOriginalGlobalPullbackMap p q ≫ pullback.snd q₁ q₂ =
    cocartesianStraighteningHomInterval p q ≫ intervalDiagramGlobalDiagramRestriction P Q
      (cocartesianFiniteHornOver 2 1) := by
  rw [cocartesianTwoBoundaryOriginalGlobalPullbackMap, Category.assoc,
    cocartesianTwoBoundaryTargetPresentationIso_hom_snd, Category.assoc,
    intervalDiagramGlobalDiagramRestriction_naturality]
  rfl

end SerrePositivity.InfinityCategories
