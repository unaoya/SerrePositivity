module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryProjections
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundarySimplexOverMaps
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativeRestrictionMap

/-!
概要：標準一単体上の全 native Hom から境界比較への作用を、同じ二端点の積で計算する。
方針：既存の境界比較の両射影と反変関手の合成則を使う。
規約：元の一単体上の全局所 Hom を保持する。
使われ方：境界への全局所比較の指定自然性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "N" => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
  SSet.uliftFunctor
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 同じ面側の端点への全局所作用。 -/
def cocartesianOneBoundaryLocalSourceFace :=
  (N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.faceSimplexOverMap 0 i σ).op ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q

/-- 同じホーン側の端点への全局所作用。 -/
def cocartesianOneBoundaryLocalSourceHorn :=
  (N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornSimplexOverMap 0 i σ).op ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneHornHomComparison i σ p q

/-- 同じ境界比較の積表示は、一単体の全局所 Hom 上の同じ二端点作用の対。 -/
lemma cocartesianOneBoundaryHomComparison_localSourceProduct :
    ((N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ).op ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison i σ p q) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryIntervalProductIso i σ P Q).hom =
    lift (cocartesianOneBoundaryLocalSourceFace i σ p q)
      (cocartesianOneBoundaryLocalSourceHorn i σ p q) := by
  apply CartesianMonoidalCategory.hom_ext
  · have h := congrArg (fun k ↦ (N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ).op ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison_face i σ p q)
    have hr : (N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ).op ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p.val.hom q.val.hom
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.faceInclusion 0 i σ) = (N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.faceSimplexOverMap 0 i σ).op := by
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre_map_comp p.val.hom q.val.hom
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.faceInclusion 0 i σ) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ)).trans
          (congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.face 0 i σ ⟶ Over.mk σ ↦
            (N).map f.op) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.faceSimplexOverMap_comp 0 i σ))
    have he := congrArg (fun k ↦ k ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q) hr
    have hp := (lift_fst (cocartesianOneBoundaryLocalSourceFace i σ p q)
      (cocartesianOneBoundaryLocalSourceHorn i σ p q)).symm
    simpa only [Category.assoc, cocartesianOneBoundaryLocalSourceFace,
      cocartesianOneBoundaryLocalSourceHorn, Over.mk_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor,
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.face] using (h.trans ((Category.assoc _ _ _).symm.trans he)).trans hp
  · have h := congrArg (fun k ↦ (N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ).op ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison_horn i σ p q)
    have hr : (N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ).op ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p.val.hom q.val.hom
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion 0 i σ) = (N).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornSimplexOverMap 0 i σ).op := by
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre_map_comp p.val.hom q.val.hom
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion 0 i σ) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ)).trans
          (congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.horn 0 i σ ⟶ Over.mk σ ↦
            (N).map f.op) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornSimplexOverMap_comp 0 i σ))
    have he := congrArg (fun k ↦ k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneHornHomComparison i σ p q) hr
    have hp := (lift_snd (cocartesianOneBoundaryLocalSourceFace i σ p q)
      (cocartesianOneBoundaryLocalSourceHorn i σ p q)).symm
    simpa only [Category.assoc, cocartesianOneBoundaryLocalSourceFace,
      cocartesianOneBoundaryLocalSourceHorn, Over.mk_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor,
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.face] using (h.trans ((Category.assoc _ _ _).symm.trans he)).trans hp

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
