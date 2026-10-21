module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneHornComparison

/-!
概要：一次元境界のホーン側の同じ分類比較を、元の全 Hom 作用と結ぶ。
方針：同じ点表示の両直接制限を計算し、指定された標準点上の自然性を移す。
規約：元のホーンと元の分類作用を保持する。
使われ方：両端の指定同型を対にして一次元境界の自然性を示す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ nerve C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 同じホーンの source 表示変更は、元の標準点への制限を回収する。 -/
lemma cocartesianOneHornSourceIso_original :
    cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom (HornBoundaryOver.horn 0 i σ) ≫
      (cocartesianOneHornSourceIso i σ p q).hom =
    cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
      (Over.mk (hornOnePointMap i σ)) := by
  rw [cocartesianOneHornSourceIso_hom]
  exact cocartesianPullbackNativeLiftRestriction_naturality p.val.hom q.val.hom
    (hornOnePointOverIso i σ).hom

/-- 同じホーンの target 表示変更は、元のホーンへの直接制限を回収する。 -/
lemma cocartesianOneHornTargetIso_original :
    intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (hornOnePointMap i σ)) P Q ≫
      (cocartesianOneHornTargetIso i σ p q).hom =
    intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.horn 0 i σ).hom) P Q := by
  rw [cocartesianOneHornTargetIso_hom]
  exact intervalDiagramOverPre_restriction P Q (uliftOverMorphism (hornOnePointOverIso i σ).inv)

/-- 同じホーン側の分類比較は、元の全 Hom 作用と指定関手同型で可換。 -/
def cocartesianOneHornHomComparison_originalIso :
    FunctorIso
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom (HornBoundaryOver.horn 0 i σ) ≫
        cocartesianOneHornHomComparison i σ p q)
      (cocartesianStraighteningHomInterval p q ≫
        intervalDiagramRestriction
          ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.horn 0 i σ).hom) P Q) := by
  apply F2.functorIsoOfEq
    ((cocartesianStandardSimplexHomComparison_originalIso (hornOnePointMap i σ) p q).postcomp
      (cocartesianOneHornTargetIso i σ p q).hom)
  · rw [← cocartesianOneHornSourceIso_original i σ p q]
    simp only [cocartesianOneHornHomComparison, Category.assoc]
  · rw [Category.assoc, cocartesianOneHornTargetIso_original]

end SerrePositivity.InfinityCategories
