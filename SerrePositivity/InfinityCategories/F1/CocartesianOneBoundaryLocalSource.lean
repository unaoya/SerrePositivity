module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryProjections
public import SerrePositivity.InfinityCategories.F1.HornBoundarySimplexOverMaps
public import SerrePositivity.InfinityCategories.F1.CocartesianNativeRestrictionMap

/-!
概要：標準一単体上の全 native Hom から境界比較への作用を、同じ二端点の積で計算する。
方針：既存の境界比較の両射影と反変関手の合成則を使う。
規約：元の一単体上の全局所 Hom を保持する。
使われ方：境界への全局所比較の指定自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))
local notation "N" => (cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
  SSet.uliftFunctor
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 同じ面側の端点への全局所作用。 -/
def cocartesianOneBoundaryLocalSourceFace :=
  (N).map (faceSimplexOverMap 0 i σ).op ≫
    cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q

/-- 同じホーン側の端点への全局所作用。 -/
def cocartesianOneBoundaryLocalSourceHorn :=
  (N).map (hornSimplexOverMap 0 i σ).op ≫ cocartesianOneHornHomComparison i σ p q

/-- 同じ境界比較の積表示は、一単体の全局所 Hom 上の同じ二端点作用の対。 -/
lemma cocartesianOneBoundaryHomComparison_localSourceProduct :
    ((N).map (boundarySimplexOverMap 0 σ).op ≫ cocartesianOneBoundaryHomComparison i σ p q) ≫
      (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom =
    lift (cocartesianOneBoundaryLocalSourceFace i σ p q)
      (cocartesianOneBoundaryLocalSourceHorn i σ p q) := by
  apply CartesianMonoidalCategory.hom_ext
  · have h := congrArg (fun k ↦ (N).map (boundarySimplexOverMap 0 σ).op ≫ k)
      (cocartesianOneBoundaryHomComparison_face i σ p q)
    have hr : (N).map (boundarySimplexOverMap 0 σ).op ≫
        cocartesianPullbackNativeLiftPre p.val.hom q.val.hom
          (HornBoundaryOver.faceInclusion 0 i σ) = (N).map (faceSimplexOverMap 0 i σ).op := by
      exact (cocartesianPullbackNativeLiftPre_map_comp p.val.hom q.val.hom
        (HornBoundaryOver.faceInclusion 0 i σ) (boundarySimplexOverMap 0 σ)).trans
          (congrArg (fun f : HornBoundaryOver.face 0 i σ ⟶ Over.mk σ ↦
            (N).map f.op) (faceSimplexOverMap_comp 0 i σ))
    have he := congrArg (fun k ↦ k ≫
      cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q) hr
    have hp := (lift_fst (cocartesianOneBoundaryLocalSourceFace i σ p q)
      (cocartesianOneBoundaryLocalSourceHorn i σ p q)).symm
    simpa only [Category.assoc, cocartesianOneBoundaryLocalSourceFace,
      cocartesianOneBoundaryLocalSourceHorn, Over.mk_hom, intervalDiagramOverFunctor,
      HornBoundaryOver.face] using (h.trans ((Category.assoc _ _ _).symm.trans he)).trans hp
  · have h := congrArg (fun k ↦ (N).map (boundarySimplexOverMap 0 σ).op ≫ k)
      (cocartesianOneBoundaryHomComparison_horn i σ p q)
    have hr : (N).map (boundarySimplexOverMap 0 σ).op ≫
        cocartesianPullbackNativeLiftPre p.val.hom q.val.hom
          (HornBoundaryOver.hornInclusion 0 i σ) = (N).map (hornSimplexOverMap 0 i σ).op := by
      exact (cocartesianPullbackNativeLiftPre_map_comp p.val.hom q.val.hom
        (HornBoundaryOver.hornInclusion 0 i σ) (boundarySimplexOverMap 0 σ)).trans
          (congrArg (fun f : HornBoundaryOver.horn 0 i σ ⟶ Over.mk σ ↦
            (N).map f.op) (hornSimplexOverMap_comp 0 i σ))
    have he := congrArg (fun k ↦ k ≫ cocartesianOneHornHomComparison i σ p q) hr
    have hp := (lift_snd (cocartesianOneBoundaryLocalSourceFace i σ p q)
      (cocartesianOneBoundaryLocalSourceHorn i σ p q)).symm
    simpa only [Category.assoc, cocartesianOneBoundaryLocalSourceFace,
      cocartesianOneBoundaryLocalSourceHorn, Over.mk_hom, intervalDiagramOverFunctor,
      HornBoundaryOver.face] using (h.trans ((Category.assoc _ _ _).symm.trans he)).trans hp

end SerrePositivity.InfinityCategories
