module

public import SerrePositivity.InfinityCategories.F2.Ind.CoherentReturnPostcomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeFunctorImage
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNativeCocones
public import SerrePositivity.InfinityCategories.F1.SquareOpposite

/-!
概要：元の通常の余錐全体の coherent な表示は、豊穣関手の実際の後合成と可換。
方針：反対の錐の同じ比較を反転し、標準帰還写像の自然性で元へ戻す。
規約：join からの射の全次数の等式。脚や頂点だけの比較で代用しない。
使われ方：strict right straightening の指定余錐の fiber 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {I : Type u} [SmallCategory I] {C D : Type v}
  [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]

/-- 余錐を写して反対にした錐の coherent な射は、元の反対の錐の同じ後合成。 -/
lemma strictCocone_oppositeCone_postcomp {F : I ⥤ C} (c : Cocone F)
    (R : EnrichedFunctor SSet.{u} C D) :
    (strictCoherentCone c.op).val ≫ coherentNerveMap (simplicialEnrichedOpposite R) =
      (strictCoherentCone ((coherentEnrichedUnderlyingFunctor R).mapCocone c).op).val := by
  change strictCoherentConeMap c.op ≫ _ = strictCoherentConeMap _
  rw [strictCoherentConeMap_postcomp, coherentUnderlying_opposite]
  rfl

/-- 元の native な通常の余錐の全 join 射は、豊穣関手の実際の後合成で保たれる。 -/
lemma strictNativeCocone_postcomp_val {F : I ⥤ C} (c : Cocone F)
    (R : EnrichedFunctor SSet.{u} C D) :
    (strictNativeCocone c).val ≫ coherentNerveMap R =
      (strictNativeCocone ((coherentEnrichedUnderlyingFunctor R).mapCocone c)).val := by
  rw [strictNativeCocone_val, strictNativeCocone_val]
  unfold strictCoherentCocone
  rw [coherentCoconePost_val, coherentCoconePost_val]
  change (joinMap (strictCoconeIndexIso I).hom (𝟙 Δ[0]) ≫
    (strictCoherentCone c.op).reverseCocone.val) ≫
      (coherentOppositeReturnIso C).hom ≫ coherentNerveMap R =
    (joinMap (strictCoconeIndexIso I).hom (𝟙 Δ[0]) ≫
      (strictCoherentCone
        ((coherentEnrichedUnderlyingFunctor R).mapCocone c).op).reverseCocone.val) ≫
        (coherentOppositeReturnIso D).hom
  rw [JoinCone.reverseCocone_val, JoinCone.reverseCocone_val]
  simp only [Category.assoc]
  rw [← coherentReturn_postcomp R,
    ← Category.assoc (SSet.opFunctor.map (strictCoherentCone c.op).val)
      (SSet.opFunctor.map (coherentNerveMap (simplicialEnrichedOpposite R)))
      (coherentOppositeReturnIso D).hom,
    ← CategoryTheory.Functor.map_comp, strictCocone_oppositeCone_postcomp]

end SerrePositivity.InfinityCategories.F2.Ind
