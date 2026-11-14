module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomTypedMapBridges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomLiftedPathReflection
/-!
概要：実包含後の比較と経路の反映を、同じ型付き全関手射で扱う。
方針：一般の関手空間で前後合成を回収し、元の指定値を保つ。
規約：可逆性は追加しない。使われ方：K-flat 合成比較の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorHom_two_three_reflect_typed_precomp {X Y X' Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z] (i : Y ⟶ Z) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i) (J : X ⟶ X')
    {f g h t k : X ⟶ Y} {f' g' h' t' k' : X' ⟶ Z}
    (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g k)
    (q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f h) (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom h t) (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom t k)
    (c' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g') (r' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g' k')
    (q' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' h') (d' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom h' t') (a' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom t' k')
    (hf : f ≫ i = J ≫ f') (hg : g ≫ i = J ≫ g') (hh : h ≫ i = J ≫ h')
    (ht : t ≫ i = J ≫ t') (hk : k ≫ i = J ≫ k')
    (hc : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g i c) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' g' J c'))
    (hr : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp g k i r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp g' k' J r'))
    (hq : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f h i q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' h' J q'))
    (hd : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp h t i d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp h' t' J d'))
    (ha : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp t k i a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp t' k' J a'))
    (he : c' ≫ r' = q' ≫ d' ≫ a') : c ≫ r = q ≫ d ≫ a := by
  have hp := congrArg (fun e => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' k' J e) he
  have hp' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' g' J c' ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp g' k' J r' =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' h' J q' ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp h' t' J d' ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp t' k' J a' := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp, CategoryTheory.Functor.map_comp] using! hp
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_two_three_reflect_postcomp i hi c r q d a
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' g' J c') (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp g' k' J r')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' h' J q') (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp h' t' J d')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp t' k' J a') hf hg hh ht hk
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_map_heq f g i c).symm.trans hc)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_map_heq g k i r).symm.trans hr)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_map_heq f h i q).symm.trans hq)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_map_heq h t i d).symm.trans hd)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_map_heq t k i a).symm.trans ha) hp'
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
