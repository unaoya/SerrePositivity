module

public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalNaturality
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedHomIntervalNaturality

/-!
概要：元の coherent Hom の全区間族は、同じ豊穣 Hom 作用に自然。
方針：既存の prism の自然性を、同じ区間 Hom の普遍族として表す。
規約：元の全 Hom と同じ coherent 比較を保持する。
使われ方：全局所比較の両端と元の分類作用の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の coherent 区間 Hom の普遍族は、同じ豊穣作用と厳密に可換。 -/
lemma coherentHomIntervalComparison_uncurry_enriched_naturality
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    intervalMappingUncurry (coherentHomIntervalComparison X Y) ≫ coherentNerveMap F =
      (Δ[1] ◁ (SSet.uliftFunctor.{v, u}).map (F.map X Y)) ≫
        intervalMappingUncurry (coherentHomIntervalComparison (F.obj X) (F.obj Y)) := by
  unfold coherentHomIntervalComparison
  rw [pinchedHomToIntervalMappingSpace_uncurry, pinchedHomToIntervalMappingSpace_uncurry]
  exact coherentRightHomInterval_enriched_naturality F X Y

end SerrePositivity.InfinityCategories
