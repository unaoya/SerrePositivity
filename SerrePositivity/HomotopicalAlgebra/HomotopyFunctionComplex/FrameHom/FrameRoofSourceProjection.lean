module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofSource
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerEvaluationPrism

/-!
# 元の frame 屋根比較の全 slice 射影

概要：同じ実屋根比較の qY slice への射影を元の通常の右脚から回収する。
方針：元の pullback.lift の第一射影と Over nerve 同型の射影式を使う。
規約：元の q・元の点図式・全単体を保持する。
使われ方：実評価三角形の右脚と元の通常の自然変換との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E)

lemma frameRoofMap_over : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap A Y q ≫ pullback.fst _ _ =
    nerveMap (CostructuredArrow.toOver A Y) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) q := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap, Category.assoc]
  change (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSourceIso A Y).hom ≫ (pullback.lift _ _ _ ≫ pullback.fst _ _) = _
  rw [pullback.lift_fst]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  rw [← Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofSourceIso_over, Category.assoc]

def frameRoofRightSliceMap : nerve (CostructuredArrow A Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) :=
  nerveMap (CostructuredArrow.toOver A Y) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso Y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) q ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetSlicePointIso Y q).hom

lemma frameRoofMap_normalizedOver : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap A Y q ≫ pullback.fst _ _ ≫
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetSlicePointIso Y q).hom = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofRightSliceMap A Y q := by
  rw [← Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap_over]
  rfl

lemma roofCornerSourceSliceMap_eq_source (b : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTarget A Y q) _⦋0⦌)
    {S : SSet.{u}} (f : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b)
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q)) :
    f ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerSourceSliceMap A Y q b =
      (f ≫ pullback.snd _ _) ≫ pullback.fst _ _ ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetSlicePointIso Y q).hom :=
  (Category.assoc _ _ _).symm

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
