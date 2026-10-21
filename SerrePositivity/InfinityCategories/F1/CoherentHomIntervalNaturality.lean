module

public import SerrePositivity.InfinityCategories.F1.CoherentHomEnrichedNaturality
public import SerrePositivity.InfinityCategories.F1.CoherentHomEquivalence
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostHomCriterion

/-!
概要：元の豊穣 Hom から区間 Hom への比較を、豊穣関手の同じ作用と結ぶ。
方針：標準の coherent Hom 比較と pinched・区間模型の自然性を合成する。
規約：端点は同じ標準頂点へ等号で正規化する。
使われ方：元の分類写像の Hom 作用を成分評価で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の豊穣 Hom を、同じ二つの対象の coherent な区間 Hom に写す標準比較。 -/
def coherentHomIntervalComparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⟶
      intervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y) :=
  coherentHomComparison X Y ≫
    pinchedHomToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y)

/-- 局所 Kan な場合、同じ標準の区間 Hom 比較は同値。 -/
lemma coherentHomIntervalComparison_isQCatEquivalence {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    (X Y : C) : IsQCatEquivalence (coherentHomIntervalComparison X Y) :=
  (coherentHomComparison_isQCatEquivalence X Y).comp
    (pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _)

/-- 同じ区間 Hom 比較は、豊穣関手の Hom 作用と実際の coherent な後合成を結ぶ。 -/
lemma coherentHomIntervalComparison_enriched_naturality
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (H : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    coherentHomIntervalComparison X Y ≫
      intervalMappingPostOfEq (coherentNerveMap H) (coherentNerveVertex X)
        (coherentNerveVertex Y) (coherentNerveMap_vertex H X) (coherentNerveMap_vertex H Y) =
    (SSet.uliftFunctor.{v, u}).map (H.map X Y) ≫
      coherentHomIntervalComparison (H.obj X) (H.obj Y) := by
  unfold coherentHomIntervalComparison
  rw [Category.assoc, ← pinchedHomToIntervalMappingSpace_postOfEq, ← Category.assoc]
  change (coherentHomComparison X Y ≫ coherentPinchedHomMap H X Y) ≫ _ = _
  rw [coherentHomComparison_enriched_naturality, Category.assoc]

end SerrePositivity.InfinityCategories
