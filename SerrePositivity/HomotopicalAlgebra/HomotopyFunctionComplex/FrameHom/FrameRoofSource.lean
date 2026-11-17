module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofComparisonTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalComposition

/-!
# 元の frame の実屋根比較の始域を全固定終域の矢で表す

概要：元の native な slice 引き戻しを CostructuredArrow の nerve と厳密に同定する。
方針：元の左 Kan 形状比較と引き戻しの対称同型を合成する。
規約：次数射影・元の終域への矢・同じ q の屋根比較を保持する。
使われ方：sourceFrameHom の既存弱比較を実右 Kan cofinality へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.InfinityCategories
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)

abbrev roofSource := pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)))
  (nerveMap A)

def roofSourceIso : nerve (CostructuredArrow A Y) ≅ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSource A Y :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso A Y ≪≫ pullbackSymmetry _ _

lemma roofSourceIso_degree : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSourceIso A Y).hom ≫ pullback.snd _ _ =
    nerveMap (CostructuredArrow.proj A Y) := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSourceIso, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso_hom_projection A Y

lemma roofSourceIso_over : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSourceIso A Y).hom ≫ pullback.fst _ _ =
    nerveMap (CostructuredArrow.toOver A Y) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso Y).hom := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSourceIso, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeMap_over A Y

variable {E : SSet.{u}} (q : nerve C ⟶ E)

def frameRoofMap : nerve (CostructuredArrow A Y) ⟶
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) ≫ q))
      (nerveMap A ≫ q) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSourceIso A Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap q (nerveMap A)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))

lemma frameRoofMap_degree : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap A Y q ≫ pullback.snd _ _ =
    nerveMap (CostructuredArrow.proj A Y) := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap, Category.assoc]
  change (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSourceIso A Y).hom ≫
    (pullback.lift _ _ _ ≫ pullback.snd _ _) = _
  rw [pullback.lift_snd]
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSourceIso_degree A Y

lemma frameRoofMap_isLeftCofinal_iff_raw : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap A Y q) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap q (nerveMap A)
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_isIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSourceIso A Y).hom
  constructor
  · intro h
    exact hi.cancel_left h
  · intro h
    exact hi.comp h

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
