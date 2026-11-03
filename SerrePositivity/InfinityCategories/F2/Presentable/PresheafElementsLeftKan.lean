module

public import SerrePositivity.InfinityCategories.F2.Ind.IndDensityKanCoconeMap
public import SerrePositivity.InfinityCategories.F1.Ind.ElementsYonedaSliceEquivalence
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes

/-!
概要：全前層の元の左 Kan 添字と、小さい元の圏の密度比較を同じ全余錐で同定する。
方針：Yoneda comma の引き戻し因子を交換し、公開済みの密度比較を合成する。
規約：元の指定前層頂点と全余錐の写像を厳密に保持する。
使われ方：前層上の全関手を密度により左 Kan 延長と判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 概要：元の小さい元の圏から、同じ前層頂点における元の左 Kan 添字への密度比較。
方針：Yoneda comma の引き戻し因子を交換し、公開済みの密度比較を合成する。
規約：元の指定前層頂点と全余錐の写像を厳密に保持する。
使われ方：前層上の全関手を密度により左 Kan 延長と判定する。 -/
def presheafElementsLeftKanComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F) ⟶
      leftKanShape (yonedaInfinityMap C) (functorVertex F) :=
  presheafElementsYonedaSliceComparison F ≫
    (pullbackSymmetry (yonedaInfinityMap C)
      (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F)))).inv

/-- 概要：同じ元の密度比較自身が同値。
方針：Yoneda comma の引き戻し因子を交換し、公開済みの密度比較を合成する。
規約：元の指定前層頂点と全余錐の写像を厳密に保持する。
使われ方：前層上の全関手を密度により左 Kan 延長と判定する。 -/
lemma presheafElementsLeftKanComparison_isQCatEquivalence :
    IsQCatEquivalence (presheafElementsLeftKanComparison F) :=
  (presheafElementsYonedaSliceComparison_isQCatEquivalence F).comp
    (qCatEquivalenceOfIso (pullbackSymmetry (yonedaInfinityMap C)
      (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F)))).symm).isQCatEquivalence

/-- 概要：同じ密度比較による元の標準 Kan 全余錐の制限は、元の全密度余錐そのもの。
方針：Yoneda comma の引き戻し因子を交換し、公開済みの密度比較を合成する。
規約：元の指定前層頂点と全余錐の写像を厳密に保持する。
使われ方：前層上の全関手を密度により左 Kan 延長と判定する。 -/
lemma presheafElementsLeftKanComparison_coconeMap :
    joinMap (presheafElementsLeftKanComparison F) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      (leftKanCanonicalCocone (yonedaInfinityMap C) (𝟙 _) (functorVertex F)).val =
        (presheafDensityCocone F).val := by
  simp only [presheafElementsLeftKanComparison, joinMap_comp_fixed, Category.assoc,
    leftKanCanonicalCocone, Category.comp_id]
  rw [← sliceOverUncurry_precomp]
  erw [pullbackSymmetry_inv_comp_snd]
  exact presheafElementsYonedaSliceComparison_coconeMap F

end SerrePositivity.InfinityCategories.HomotopyLimits
