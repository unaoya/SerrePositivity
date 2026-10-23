module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryProjections

/-!
概要：元の大域 Hom から一次元境界比較を通した target の積表示は、同じ両端の比較の対。
方針：二つの実際の射影と元の native 制限の厳密な自然性を計算する。
規約：元の全相対 Hom の作用と端点を保持する。
使われ方：一次元境界比較の元の大域作用との指定同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ nerve C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "RB" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (HornBoundaryOver.apex 0 σ)

/-- 元の全 Hom 上で、同じ境界比較の積表示は同じ両端比較の対。 -/
lemma cocartesianOneBoundaryHomComparison_originalSourceProduct :
    (RB ≫ cocartesianOneBoundaryHomComparison i σ p q) ≫
      (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom =
    lift
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (HornBoundaryOver.face 0 i σ) ≫
          cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q)
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (HornBoundaryOver.horn 0 i σ) ≫ cocartesianOneHornHomComparison i σ p q) := by
  apply CartesianMonoidalCategory.hom_ext
  · have h := congrArg (fun k ↦ RB ≫ k) (cocartesianOneBoundaryHomComparison_face i σ p q)
    have hr := cocartesianPullbackNativeLiftRestriction_naturality p.val.hom q.val.hom
      (HornBoundaryOver.faceInclusion 0 i σ)
    have he := congrArg (fun k ↦ k ≫
      cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q) hr
    have hp := (lift_fst
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (HornBoundaryOver.face 0 i σ) ≫
          cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q)
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (HornBoundaryOver.horn 0 i σ) ≫ cocartesianOneHornHomComparison i σ p q)).symm
    simpa only [Category.assoc, Over.mk_hom, intervalDiagramOverFunctor, HornBoundaryOver.face] using
      (h.trans ((Category.assoc _ _ _).symm.trans he)).trans hp
  · have h := congrArg (fun k ↦ RB ≫ k) (cocartesianOneBoundaryHomComparison_horn i σ p q)
    have hr := cocartesianPullbackNativeLiftRestriction_naturality p.val.hom q.val.hom
      (HornBoundaryOver.hornInclusion 0 i σ)
    have he := congrArg (fun k ↦ k ≫ cocartesianOneHornHomComparison i σ p q) hr
    have hp := (lift_snd
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (HornBoundaryOver.face 0 i σ) ≫
          cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q)
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (HornBoundaryOver.horn 0 i σ) ≫ cocartesianOneHornHomComparison i σ p q)).symm
    simpa only [Category.assoc, Over.mk_hom, intervalDiagramOverFunctor, HornBoundaryOver.face] using
      (h.trans ((Category.assoc _ _ _).symm.trans he)).trans hp

end SerrePositivity.InfinityCategories
