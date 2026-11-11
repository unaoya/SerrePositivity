module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndDensityKanCoconeMap
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.ElementsYonedaSliceEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes

/-!
概要：全前層の元の左 Kan 添字と、小さい元の圏の密度比較を同じ全余錐で同定する。
方針：Yoneda comma の引き戻し因子を交換し、公開済みの密度比較を合成する。
規約：元の指定前層頂点と全余錐の写像を厳密に保持する。
使われ方：前層上の全関手を密度により左 Kan 延長と判定する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 概要：元の小さい元の圏から、同じ前層頂点における元の左 Kan 添字への密度比較。
方針：Yoneda comma の引き戻し因子を交換し、公開済みの密度比較を合成する。
規約：元の指定前層頂点と全余錐の写像を厳密に保持する。
使われ方：前層上の全関手を密度により左 Kan 延長と判定する。 -/
def presheafElementsLeftKanComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafElementsYonedaSliceComparison F ≫
    (pullbackSymmetry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)))).inv

/-- 概要：同じ元の密度比較自身が同値。
方針：Yoneda comma の引き戻し因子を交換し、公開済みの密度比較を合成する。
規約：元の指定前層頂点と全余錐の写像を厳密に保持する。
使われ方：前層上の全関手を密度により左 Kan 延長と判定する。 -/
lemma presheafElementsLeftKanComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (presheafElementsLeftKanComparison F) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafElementsYonedaSliceComparison_isQCatEquivalence F).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (pullbackSymmetry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)))).symm).isQCatEquivalence

/-- 概要：同じ密度比較による元の標準 Kan 全余錐の制限は、元の全密度余錐そのもの。
方針：Yoneda comma の引き戻し因子を交換し、公開済みの密度比較を合成する。
規約：元の指定前層頂点と全余錐の写像を厳密に保持する。
使われ方：前層上の全関手を密度により左 Kan 延長と判定する。 -/
lemma presheafElementsLeftKanComparison_coconeMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (presheafElementsLeftKanComparison F) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone F).val := by
  simp only [presheafElementsLeftKanComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.joinMap_comp_fixed, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone, Category.comp_id]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp]
  erw [pullbackSymmetry_inv_comp_snd]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafElementsYonedaSliceComparison_coconeMap F

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
