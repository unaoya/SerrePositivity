module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoPrecompositionReflection
/-!
概要：同じ比較四角形を型付き前後合成へ送り、全前合成から等式を反映する。
方針：実 h Fun の関手性と完全充満な前合成の単射性を使う。
規約：可逆性は追加しない。使われ方：元の κ の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
lemma functorHomPostcomp_iso_square {X Y Z : SSet.{u}} {f f' g g' : X ⟶ Y}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (c' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f f')
    (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g g') (H : Y ⟶ Z) (hs : c.hom ≫ r = q ≫ c'.hom) :
    (c.postcomp H).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp g g' H r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f f' H q ≫ (c'.postcomp H).hom := by
  have h := congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g' H z) hs
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed] using! h
lemma functorHomPrecomp_iso_square {X A Y : SSet.{u}} {f f' g g' : A ⟶ Y}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (c' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f f')
    (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g g') (L : X ⟶ A)
    (hs : (c.precomp L).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp g g' L r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f f' L q ≫ (c'.precomp L).hom) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g' L (c.hom ≫ r) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g' L (q ≫ c'.hom) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed] using! hs
lemma functorHomPrecomp_eq_of_isFullyFaithful {X A Y : SSet.{u}} [Quasicategory Y]
    (L : X ⟶ A) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre L).app Y))
    {f g : A ⟶ Y} (a b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g)
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g L a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g L b) : a = b := by
  apply hL.toHoFullyFaithful.map_injective
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp] using! h
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
