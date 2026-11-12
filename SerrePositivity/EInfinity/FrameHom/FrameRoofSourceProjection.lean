module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofSource
public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerEvaluationPrism

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
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E)

lemma frameRoofMap_over : frameRoofMap A Y q ≫ pullback.fst _ _ =
    nerveMap (CostructuredArrow.toOver A Y) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverIso Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) q := by
  rw [frameRoofMap, Category.assoc]
  change (roofSourceIso A Y).hom ≫ (pullback.lift _ _ _ ≫ pullback.fst _ _) = _
  rw [pullback.lift_fst]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  rw [← Category.assoc, roofSourceIso_over, Category.assoc]

def frameRoofRightSliceMap : nerve (CostructuredArrow A Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) :=
  nerveMap (CostructuredArrow.toOver A Y) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverIso Y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) q ≫
      (roofTargetSlicePointIso Y q).hom

lemma frameRoofMap_normalizedOver : frameRoofMap A Y q ≫ pullback.fst _ _ ≫
    (roofTargetSlicePointIso Y q).hom = frameRoofRightSliceMap A Y q := by
  rw [← Category.assoc, frameRoofMap_over]
  rfl

lemma roofCornerSourceSliceMap_eq_source (b : (roofTarget A Y q) _⦋0⦌)
    {S : SSet.{u}} (f : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b)
      (roofTargetProjection A Y q)) :
    f ≫ roofCornerSourceSliceMap A Y q b =
      (f ≫ pullback.snd _ _) ≫ pullback.fst _ _ ≫ (roofTargetSlicePointIso Y q).hom :=
  (Category.assoc _ _ _).symm

end SerrePositivity.EInfinity.FrameHom.FrameArrows
