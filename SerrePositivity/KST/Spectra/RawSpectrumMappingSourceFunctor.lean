module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPreNaturality
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreeIntervalBoundary

/-!
概要：一般の Kan 列への元の点つき Hom を、BF 源についての厳密な前層へまとめる。
方針：元の合成から作った前合成の恒等・合成法則を各段で検査する。
規約：通常の圏上の前層。豊穣な自然性は別に証明する。使われ方：Hom-end の表現可能性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 源の恒等射による点つき前合成は恒等。 -/
lemma pointedPre_id (X : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    pointedPre (𝟙 X) Z = 𝟙 (pointedSpace X Z) := by
  apply pointed_hom_ext X Z
  intro n
  rw [pointedPre_evaluation, Category.id_comp]
  change pointedEvaluation X Z n ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (𝟙 (X.level n).space) (Z.level n).space = _
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, MonoidalClosed.pre_id,
    NatTrans.id_app]
  exact Category.comp_id (pointedEvaluation X Z n)

/-- 源の射の合成による点つき前合成は逆順の合成。 -/
lemma pointedPre_comp {X Y W : OmegaSpectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (Z : KanSequence.{u}) :
    pointedPre (f ≫ g) Z = pointedPre g Z ≫ pointedPre f Z := by
  apply pointed_hom_ext X Z
  intro n
  rw [pointedPre_evaluation]
  conv_rhs =>
    rw [Category.assoc, pointedPre_evaluation, ← Category.assoc,
      pointedPre_evaluation, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]
  rfl

/-- 一般の Kan 列への元の整合写像空間の、BF 源についての厳密な点つき前層。 -/
def sourceFunctor (Z : KanSequence.{u}) : OmegaSpectrum.{u}ᵒᵖ ⥤ PointedSimplicialSet.{u} where
  obj X := pointedSpace X.unop Z
  map f := pointedPre f.unop Z
  map_id X := pointedPre_id X.unop Z
  map_comp f g := pointedPre_comp g.unop f.unop Z

end SerrePositivity.KST.Spectra.RawSpectrumMapping
