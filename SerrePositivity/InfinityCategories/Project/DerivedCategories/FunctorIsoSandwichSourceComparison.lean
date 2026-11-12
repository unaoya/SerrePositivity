module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSandwichTail
/-!
概要：元の一般合成子を始域同値に沿う指定比較正方形へ接続する。
方針：同じ比較値・前後合成の交換則を保持する。
規約：同値の三角式は仮定しない。使われ方：一般 cell 合成子の五角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIsoSandwichCompositor_source_comparison {X A B Y C Z : SSet.{u}}
    [Quasicategory A] [Quasicategory Z]
    (L : A ⟶ X) (s : X ⟶ A) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ s) (𝟙 A))
    (h : B ⟶ Y) (i : Y ⟶ B) (t : C ⟶ Z) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (h ≫ i) (𝟙 B))
    (F : X ⟶ Y) (G : Y ⟶ Z) (M : A ⟶ B) (N : B ⟶ C) (T : A ⟶ C)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (s ≫ M ≫ h)) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (i ≫ N ≫ t))
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (M ≫ N) T) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor s h i t e F G M N T a b k).precomp L ≪≫
        d.postcomp (T ≫ t) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L h t F M G N
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoInverseSourceComparison L s d F (M ≫ h) a)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoInverseSourceComparison h i e G (N ≫ t) b) ≪≫ k.postcomp t := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoInverseSource_transport L s d (F ≫ G) (M ≫ h ≫ G) (T ≫ t)
    (a.postcomp G) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichTail h i t e G M N T b k)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_tail, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoInverseSourceComparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichTail, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp,
    Category.assoc, Iso.trans_assoc] using! hs
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
