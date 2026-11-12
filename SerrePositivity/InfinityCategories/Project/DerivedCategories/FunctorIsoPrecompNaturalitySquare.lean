module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedNaturalityTransport
/-!
概要：元の kernel 合成子の右変数自然性を、同じ通常比較と raw 経路で照合する。
方針：元の指定比較と射の値を保持し、全関手圏の実作用と可換四角形を使う。
規約：後続 kernel の平坦性・射の可逆性は要求しない。使われ方：模型変更の整合性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
lemma functorHomPrecomp_iso_square_forward {X A Y : SSet.{u}}
    {f f' g g' : A ⟶ Y} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (c' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g')
    (q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f f') (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g g') (L : X ⟶ A)
    (hs : c.hom ≫ r = q ≫ c'.hom) :
    (c.precomp L).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp g g' L r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f f' L q ≫ (c'.precomp L).hom := by
  have h := congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g' L z) hs
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed] using! h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
