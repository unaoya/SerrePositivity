module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichTail
/-!
概要：元の一般合成子を始域同値に沿う指定比較正方形へ接続する。
方針：同じ比較値・前後合成の交換則を保持する。
規約：同値の三角式は仮定しない。使われ方：一般 cell 合成子の五角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIsoSandwichCompositor_source_comparison {X A B Y C Z : SSet.{u}}
    [Quasicategory A] [Quasicategory Z]
    (L : A ⟶ X) (s : X ⟶ A) (d : FunctorIso (L ≫ s) (𝟙 A))
    (h : B ⟶ Y) (i : Y ⟶ B) (t : C ⟶ Z) (e : FunctorIso (h ≫ i) (𝟙 B))
    (F : X ⟶ Y) (G : Y ⟶ Z) (M : A ⟶ B) (N : B ⟶ C) (T : A ⟶ C)
    (a : FunctorIso F (s ≫ M ≫ h)) (b : FunctorIso G (i ≫ N ≫ t))
    (k : FunctorIso (M ≫ N) T) :
    (functorIsoSandwichCompositor s h i t e F G M N T a b k).precomp L ≪≫
        d.postcomp (T ≫ t) =
      comparisonCompositionIso L h t F M G N
        (functorIsoInverseSourceComparison L s d F (M ≫ h) a)
        (functorIsoInverseSourceComparison h i e G (N ≫ t) b) ≪≫ k.postcomp t := by
  have hs := functorIsoInverseSource_transport L s d (F ≫ G) (M ≫ h ≫ G) (T ≫ t)
    (a.postcomp G) (functorIsoSandwichTail h i t e G M N T b k)
  simpa only [functorIsoSandwichCompositor_tail, functorIsoInverseSourceComparison,
    functorIsoSandwichTail, comparisonCompositionIso, F2.functorIso_precomp_trans,
    F2.functorIso_postcomp_trans, F2.functorIso_precomp_precomp,
    F2.functorIso_precomp_postcomp, F2.functorIso_postcomp_postcomp,
    Category.assoc, Iso.trans_assoc] using! hs
end
end SerrePositivity.InfinityCategories
