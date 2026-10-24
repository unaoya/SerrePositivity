module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.Derived.RoofComparisonTransport
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalOpposite
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalComposition

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
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits SerrePositivity.InfinityCategories
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)

abbrev roofSource := pullback (sliceOverProjection (SSet.yonedaEquiv.symm (nerveVertex Y)))
  (nerveMap A)

def roofSourceIso : nerve (CostructuredArrow A Y) ≅ roofSource A Y :=
  SerrePositivity.InfinityCategories.F1B.nerveLeftKanShapeIso A Y ≪≫ pullbackSymmetry _ _

lemma roofSourceIso_degree : (roofSourceIso A Y).hom ≫ pullback.snd _ _ =
    nerveMap (CostructuredArrow.proj A Y) := by
  rw [roofSourceIso, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact SerrePositivity.InfinityCategories.F1B.nerveLeftKanShapeIso_hom_projection A Y

lemma roofSourceIso_over : (roofSourceIso A Y).hom ≫ pullback.fst _ _ =
    nerveMap (CostructuredArrow.toOver A Y) ≫ (SerrePositivity.InfinityCategories.F1B.nerveOverIso Y).hom := by
  rw [roofSourceIso, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact SerrePositivity.InfinityCategories.F1B.nerveLeftKanShapeMap_over A Y

variable {E : SSet.{u}} (q : nerve C ⟶ E)

def frameRoofMap : nerve (CostructuredArrow A Y) ⟶
    pullback (sliceOverProjection (SSet.yonedaEquiv.symm (nerveVertex Y) ≫ q))
      (nerveMap A ≫ q) :=
  (roofSourceIso A Y).hom ≫ rawRoofFunctorMap q (nerveMap A)
    (SSet.yonedaEquiv.symm (nerveVertex Y))

lemma frameRoofMap_degree : frameRoofMap A Y q ≫ pullback.snd _ _ =
    nerveMap (CostructuredArrow.proj A Y) := by
  rw [frameRoofMap, Category.assoc]
  change (roofSourceIso A Y).hom ≫
    (pullback.lift _ _ _ ≫ pullback.snd _ _) = _
  rw [pullback.lift_snd]
  exact roofSourceIso_degree A Y

lemma frameRoofMap_isLeftCofinal_iff_raw : IsLeftCofinal (frameRoofMap A Y q) ↔
    IsLeftCofinal (rawRoofFunctorMap q (nerveMap A)
      (SSet.yonedaEquiv.symm (nerveVertex Y))) := by
  have hi := isLeftCofinal_of_isIso (roofSourceIso A Y).hom
  constructor
  · intro h
    exact hi.cancel_left h
  · intro h
    exact hi.comp h

end SerrePositivity.EInfinity.FrameHom.FrameArrows
