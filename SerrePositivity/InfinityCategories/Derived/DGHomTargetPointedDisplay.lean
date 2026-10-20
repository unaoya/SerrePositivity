module
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetCosliceComparison
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnderlyingSpacePointed
/-!
概要：実 Hom 単位による coslice 比較を、同じ空間値 Hom 関手の pointed 表示へ送る。
方針：同じ基礎空間関手の始点固定 Tw 表示を前合成し、実射影の全単体等式を結ぶ。
規約：全 fiber の同値性は別工程。使われ方：F1 Hom 関手族との全比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] (x : C)
/-- 一般 dg 対象からの同じ R 加群値 Hom に基礎空間を適用した全関手。 -/
def dgHomTargetUnderlyingSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj (dgNerve R C) ⟶
      SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (dgNerve.map (dgHomTargetModuleLift R C x)) ≫ dgHomUnderlyingSpaceInfinity R C

/-- 同じ実 Hom 単位から構成した、元の実 coslice 全体の pointed 表示。 -/
def dgHomTargetCoslicePointedDisplay :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj (dgVertexCoslice R C x) ⟶
      PointedSpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (dgHomTargetCosliceComparison R C x) ≫
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (cosliceToTwistedArrowSource (dgHomModuleUnitVertex R C)) ≫
  dgHomUnderlyingSpacePointedDisplay R C
/-- 同じ実 pointed 表示は、同じ基礎空間値 Hom 関手を底に持つ。 -/
lemma dgHomTargetCoslicePointedDisplay_projection :
    dgHomTargetCoslicePointedDisplay R C x ≫ pointedSpaceProjection =
      (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R C)).symm
          (Simplex.vertex x))) ≫ dgHomTargetUnderlyingSpaceInfinity R C x := by
  rw [dgHomTargetCoslicePointedDisplay, Category.assoc, Category.assoc,
    dgHomUnderlyingSpacePointedDisplay_projection]
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [Category.assoc, cosliceToTwistedArrowSource_projection,
    dgHomTargetCosliceComparison_projection, Functor.map_comp, Category.assoc]
  rfl
end SerrePositivity.InfinityCategories
