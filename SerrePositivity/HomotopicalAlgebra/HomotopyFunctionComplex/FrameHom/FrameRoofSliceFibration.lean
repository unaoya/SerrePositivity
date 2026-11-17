module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofQuillenSlice
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.PointSliceCornerFibration

/-!
# 実屋根 slice の既存次数比較の Kan fibration 性

概要：実 Quillen A slice から同じ次数モデルへの元の射の全ホーンを充填する。
方針：元の相対 slice corner を指定点と Over の厳密同型で正規化する。
規約：元の指定点・次数・全錐・既存比較射を保つ。弱可縮性は別の主張。
使われ方：実 slice のホモトピー fiber 比較に必要な fibration 模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet _root_.HomotopicalAlgebra
open _root_.SerrePositivity.InfinityCategories
open _root_.SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTarget A Y q) _⦋0⦌)

def roofTargetDegreeSliceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm b ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q) ≅
      nerve (Over (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b)) :=
  eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetPoint_projection A Y q b)) ≪≫
    (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b)).symm

lemma roofTargetDegreeSliceIso_projection : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegreeSliceIso A Y q b).hom ≫
    nerveMap (Over.forget (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q) := by
  have hi : (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b)).inv ≫
      nerveMap (Over.forget (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b))) := by
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b))
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso_projection, Iso.inv_hom_id_assoc]
  exact (Category.assoc _ _ _).trans ((congrArg
    (fun f => (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetPoint_projection A Y q b))).hom ≫ f)
    hi).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverProjection_eqTransport (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetPoint_projection A Y q b)))

variable {S : SSet.{u}} (f : S ⟶ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTarget A Y q)

def roofQuillenDegreeNormalizationMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTarget (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q) f (SSet.yonedaEquiv.symm b) ⟶
      pullback (f ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q)
        (nerveMap (Over.forget (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b))) :=
  pullback.map _ _ _ _ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegreeSliceIso A Y q b).hom (𝟙 S) (𝟙 (nerve I))
    (by simpa only [Category.comp_id] using (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegreeSliceIso_projection A Y q b).symm)
    (by simp) ≫ (pullbackSymmetry _ _).hom

instance roofQuillenDegreeNormalizationMap_isIso :
    IsIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap A Y q b f) := by
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap]
  infer_instance

lemma roofQuillenDegreeNormalizationMap_source :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap A Y q b f ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  simp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap, Category.assoc,
    pullbackSymmetry_hom_comp_fst, pullback.map, pullback.lift_snd, Category.comp_id]

lemma roofQuillenDegreeNormalizationMap_over :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap A Y q b f ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegreeSliceIso A Y q b).hom := by
  simp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullback.map, pullback.lift_fst]

lemma roofQuillenSliceDegreeMap_eq_native : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenSliceDegreeMap A Y q b f =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q) f (SSet.yonedaEquiv.symm b) ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap A Y q b f := by
  apply pullback.hom_ext
  · rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenSliceDegreeMap_source, Category.assoc,
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap_snd]
  · rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenSliceDegreeMap_over, Category.assoc,
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap_over, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap_fst]
    rfl

lemma roofQuillenSliceDegreeMap_fibration [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q)] :
    Fibration (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenSliceDegreeMap A Y q b f) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.pointSliceRoofTriangleMap_fibration (SSet.yonedaEquiv.symm b)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q) f
  have h : Fibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q) f
      (SSet.yonedaEquiv.symm b) ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap A Y q b f) := inferInstance
  rw [← _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenSliceDegreeMap_eq_native] at h
  exact h

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
