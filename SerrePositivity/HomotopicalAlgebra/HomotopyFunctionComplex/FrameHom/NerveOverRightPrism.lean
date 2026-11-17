module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.NerveCoconePrism
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofFiberPinchedProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.SliceEvaluationPinched

/-!
# 通常の Over 図式の実 slice 評価は元の右脚の円柱

概要：同じ qY slice への Over 図式を評価すると、元の余錐の自然変換の像を得る。
方針：点図式の等式輸送を消し、uncurry の自然性と全 nerve prism の一致を接続する。
規約：同じ q・元の全円柱を保持し、quasicategory 性は仮定しない。
使われ方：実 corner の幾何的右脚を元の標準右脚へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
open scoped _root_.Simplicial

lemma sliceOverUncurry_pointTransport {S X : SSet.{u}} {p p' : (Δ[0] : SSet.{u}) ⟶ X}
    (h : p = p') (f : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (f ≫ (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver h)).hom) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f := by
  subst p'
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

variable {I C : Type u} [Category.{u} I] [Category.{u} C] (Y : C) (T : I ⥤ Over Y)
  {E : SSet.{u}} (q : nerve C ⟶ E)

def nerveOverRightSliceMap : nerve I ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) :=
  nerveMap T ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso Y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) q ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetSlicePointIso Y q).hom

lemma nerveOverRightSliceMap_uncurry : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.nerveOverRightSliceMap Y T q) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.overForgetCocone Y).whisker T)).val ≫ q := by
  have hpost := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_postcomp
    (nerveMap T ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso Y).hom) q
  have hpre := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso Y).hom (nerveMap T)
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverIso_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_whisker] at hpre
  simp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.nerveOverRightSliceMap, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetSlicePointIso, ← Category.assoc]
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sliceOverUncurry_pointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetPoint q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))]
  exact hpost.trans (congrArg (fun g => g ≫ q) hpre)

lemma nerveOverRightSliceMap_evaluation_h :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy
      (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.nerveOverRightSliceMap Y T q)).h =
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.overForgetCocone Y).whisker T).ι).h ≫ q := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_precomp_h, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.nerveOverRightSliceMap_uncurry]
  simpa only [Category.assoc] using congrArg (fun g => g ≫ q)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveCoconePrism_eq_natTrans (T ⋙ Over.forget Y)
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.overForgetCocone Y).whisker T))

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
