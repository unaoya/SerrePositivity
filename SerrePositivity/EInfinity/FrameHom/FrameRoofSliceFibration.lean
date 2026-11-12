module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofQuillenSlice
public import SerrePositivity.EInfinity.FrameHom.PointSliceCornerFibration

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
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)

def roofTargetDegreeSliceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm b ≫ roofTargetProjection A Y q) ≅
      nerve (Over (roofTargetDegree A Y q b)) :=
  eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (roofTargetPoint_projection A Y q b)) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverIso (roofTargetDegree A Y q b)).symm

lemma roofTargetDegreeSliceIso_projection : (roofTargetDegreeSliceIso A Y q b).hom ≫
    nerveMap (Over.forget (roofTargetDegree A Y q b)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b ≫ roofTargetProjection A Y q) := by
  have hi : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverIso (roofTargetDegree A Y q b)).inv ≫
      nerveMap (Over.forget (roofTargetDegree A Y q b)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (roofTargetDegree A Y q b))) := by
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (roofTargetDegree A Y q b))
    rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverIso_projection, Iso.inv_hom_id_assoc]
  exact (Category.assoc _ _ _).trans ((congrArg
    (fun f => (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (roofTargetPoint_projection A Y q b))).hom ≫ f)
    hi).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverProjection_eqTransport (roofTargetPoint_projection A Y q b)))

variable {S : SSet.{u}} (f : S ⟶ roofTarget A Y q)

def roofQuillenDegreeNormalizationMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTarget (roofTargetProjection A Y q) f (SSet.yonedaEquiv.symm b) ⟶
      pullback (f ≫ roofTargetProjection A Y q)
        (nerveMap (Over.forget (roofTargetDegree A Y q b))) :=
  pullback.map _ _ _ _ (roofTargetDegreeSliceIso A Y q b).hom (𝟙 S) (𝟙 (nerve I))
    (by simpa only [Category.comp_id] using (roofTargetDegreeSliceIso_projection A Y q b).symm)
    (by simp) ≫ (pullbackSymmetry _ _).hom

instance roofQuillenDegreeNormalizationMap_isIso :
    IsIso (roofQuillenDegreeNormalizationMap A Y q b f) := by
  dsimp only [roofQuillenDegreeNormalizationMap]
  infer_instance

lemma roofQuillenDegreeNormalizationMap_source :
    roofQuillenDegreeNormalizationMap A Y q b f ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  simp only [roofQuillenDegreeNormalizationMap, Category.assoc,
    pullbackSymmetry_hom_comp_fst, pullback.map, pullback.lift_snd, Category.comp_id]

lemma roofQuillenDegreeNormalizationMap_over :
    roofQuillenDegreeNormalizationMap A Y q b f ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ (roofTargetDegreeSliceIso A Y q b).hom := by
  simp only [roofQuillenDegreeNormalizationMap, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullback.map, pullback.lift_fst]

lemma roofQuillenSliceDegreeMap_eq_native : roofQuillenSliceDegreeMap A Y q b f =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap (roofTargetProjection A Y q) f (SSet.yonedaEquiv.symm b) ≫
      roofQuillenDegreeNormalizationMap A Y q b f := by
  apply pullback.hom_ext
  · rw [roofQuillenSliceDegreeMap_source, Category.assoc,
      roofQuillenDegreeNormalizationMap_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap_snd]
  · rw [roofQuillenSliceDegreeMap_over, Category.assoc,
      roofQuillenDegreeNormalizationMap_over, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap_fst]
    rfl

lemma roofQuillenSliceDegreeMap_fibration [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (roofTargetProjection A Y q)] :
    Fibration (roofQuillenSliceDegreeMap A Y q b f) := by
  have := pointSliceRoofTriangleMap_fibration (SSet.yonedaEquiv.symm b)
    (roofTargetProjection A Y q) f
  have h : Fibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap (roofTargetProjection A Y q) f
      (SSet.yonedaEquiv.symm b) ≫ roofQuillenDegreeNormalizationMap A Y q b f) := inferInstance
  rw [← roofQuillenSliceDegreeMap_eq_native] at h
  exact h

end SerrePositivity.EInfinity.FrameHom.FrameArrows
