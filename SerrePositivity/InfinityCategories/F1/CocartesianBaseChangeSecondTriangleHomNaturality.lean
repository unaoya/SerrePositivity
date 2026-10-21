module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleHomFirst

/-!
概要：同じ分解三角形の Hom の最初の面は、既存の元の Hom の底変換作用を回収する。
方針：元の coherent Hom 比較の豊穣自然性と、元の面の族の厳密な等式を使う。
規約：元の全相対 Hom の core の底変換作用そのもの。
使われ方：同じ二回目の底変換 Hom 輸送との接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 既存の元の Hom 比較は、同じ coherent な区間比較と元の path への後合成。 -/
lemma cocartesianBaseChangeHomComparison_coherentInterval
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    cocartesianBaseChangeHomComparison k p q =
      coherentHomIntervalComparison p q ≫ intervalMappingPost (cocartesianBaseChangeHomPath k)
        (coherentNerveVertex p) (coherentNerveVertex q) := by
  rw [cocartesianBaseChangeHomComparison, coherentHomIntervalComparison, Category.assoc]

/-- 最初の面への射影後の作用は、元の Hom の底変換後の既存の比較作用そのもの。 -/
lemma cocartesianBaseChangeSecondTriangleHomComparison_first
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    cocartesianBaseChangeSecondTriangleHomComparison l k p q ≫
        cocartesianBaseChangeSecondTriangleHomFirst l k p q =
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianBaseChangeHomComparison l
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) := by
  have hn := coherentHomIntervalComparison_enriched_naturality
    (cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)) p q
  rw [cocartesianBaseChangeHomComparison_coherentInterval, ← Category.assoc, ← hn, Category.assoc]
  rw [← Category.assoc]
  apply intervalMappingUncurry_injective
  rw [intervalMappingPost_uncurry, intervalMappingPostOfEq_uncurry,
    cocartesianBaseChangeSecondTriangleHomFirst, intervalMappingPostOfEq_uncurry,
    cocartesianBaseChangeSecondTriangleHomComparison_uncurry]
  have h := congrArg (fun f : CocartesianFibrationInfinity (nerve C) ⟶
    equivalencePath (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) ↦
      intervalMappingUncurry (coherentHomIntervalComparison p q) ≫ f)
        (cocartesianBaseChangeSecondEquivalenceTriangle_first l k)
  simpa only [Category.assoc, cocartesianFibrationInfinityBaseChange] using h

end SerrePositivity.InfinityCategories
