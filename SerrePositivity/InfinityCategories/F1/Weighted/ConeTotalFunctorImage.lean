module

public import SerrePositivity.InfinityCategories.F1.Weighted.CosliceFunctorImage

/-!
概要：元の weighted cone の全空間比較を、豊穣関手による後合成と可換にする。
方針：正規化した coslice の射を同じ底上の pullback へ持ち上げ、両射影で確認する。
規約：実際の weightedCoherentConeComparison とその底への射影を保持する。
使われ方：strict な係数の復元と coherent unstraightening の共同自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

variable {I : Type u} [SmallCategory I] {C D : Type v}
  [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]

/-- 同じ底上で、元の coherent cone の全空間を豊穣関手の像の全空間へ写す。 -/
def coherentConeTotalFunctorImage (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    coherentConeTotal (strictCoherentDiagram F) (coherentNerveVertex x) ⟶
      coherentConeTotal (strictCoherentDiagram (F ⋙ coherentEnrichedUnderlyingFunctor R))
        (coherentNerveVertex (R.obj x)) :=
  pullback.lift
    (pullback.fst _ _ ≫ coherentCosliceFunctorImage R x) (pullback.snd _ _) (by
      rw [Category.assoc, coherentCosliceFunctorImage_projection, ← Category.assoc,
        pullback.condition, Category.assoc]
      congr 1
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      change (enrichedFunctorOfOrderDiagram _).comp SSet R = enrichedFunctorOfOrderDiagram _
      rw [enrichedFunctorOfOrderDiagram_postcomp]
      rfl)

/-- 全空間の後合成は、同じ coslice の実際の後合成を第一射影で回収する。 -/
lemma coherentConeTotalFunctorImage_fst (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D)
    (x : C) :
    coherentConeTotalFunctorImage F R x ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ coherentCosliceFunctorImage R x := pullback.lift_fst _ _ _

/-- 全空間の後合成は、元の底への射影を厳密に保つ。 -/
lemma coherentConeTotalFunctorImage_projection (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D)
    (x : C) :
    coherentConeTotalFunctorImage F R x ≫
      coherentConeProjection (strictCoherentDiagram (F ⋙ coherentEnrichedUnderlyingFunctor R))
        (coherentNerveVertex (R.obj x)) =
      coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x) :=
  pullback.lift_snd _ _ _

/-- 元の比較射の coslice 射影は、同じ weighted coslice 比較そのもの。 -/
lemma weightedCoherentConeComparison_fst (F : I ⥤ C) (x : C) :
    weightedCoherentConeComparison F x ≫
      pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (strictCoherentDiagram F) = weightedCosliceComparison F x :=
  pullback.lift_fst _ _ _

/-- 元の weighted cone の比較射は、全空間でも豊穣関手による後合成と厳密に可換。 -/
lemma weightedCoherentConeComparison_functorImage (F : I ⥤ C)
    (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    weightedCoherentConeComparison F x ≫ coherentConeTotalFunctorImage F R x =
      (SSet.uliftFunctor.{v, u}).map
        (weightedNerveMap (Functor.whiskerRight (weightedHomFunctorImage F R x) SSet.opFunctor)) ≫
        weightedCoherentConeComparison (F ⋙ coherentEnrichedUnderlyingFunctor R) (R.obj x) := by
  apply pullback.hom_ext
  · rw [Category.assoc, coherentConeTotalFunctorImage_fst, ← Category.assoc,
      weightedCoherentConeComparison_fst, Category.assoc, weightedCoherentConeComparison_fst]
    exact weightedCosliceComparison_functorImage F R x
  · change (weightedCoherentConeComparison F x ≫ coherentConeTotalFunctorImage F R x) ≫
      coherentConeProjection (strictCoherentDiagram (F ⋙ coherentEnrichedUnderlyingFunctor R))
        (coherentNerveVertex (R.obj x)) =
      ((SSet.uliftFunctor.{v, u}).map
        (weightedNerveMap (Functor.whiskerRight (weightedHomFunctorImage F R x) SSet.opFunctor)) ≫
        weightedCoherentConeComparison (F ⋙ coherentEnrichedUnderlyingFunctor R) (R.obj x)) ≫
      coherentConeProjection (strictCoherentDiagram (F ⋙ coherentEnrichedUnderlyingFunctor R))
        (coherentNerveVertex (R.obj x))
    rw [Category.assoc, coherentConeTotalFunctorImage_projection,
      Category.assoc, weightedCoherentConeComparison_over, weightedCoherentConeComparison_over,
      ← Functor.map_comp, weightedNerveMap_projection]

end SerrePositivity.InfinityCategories
