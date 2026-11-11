module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTwoThreeTransport
/-!
概要：完全充満な後合成から、任意全関手射の二辺と三辺の等式を反映する。
方針：同じ全関手射の指定値と全端点の異種等式を保つ。
規約：可逆性は不要。使われ方：K-flat 合成比較と κ の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
lemma functorHom_two_three_reflect_postcomp {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z] (i : Y ⟶ Z) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i)
    {f g h t k : X ⟶ Y} {f' g' h' t' k' : X ⟶ Z}
    (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g k)
    (q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f h) (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom h t) (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom t k)
    (c' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g') (r' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g' k')
    (q' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' h') (d' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom h' t') (a' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom t' k')
    (hf : f ≫ i = f') (hg : g ≫ i = g') (hh : h ≫ i = h')
    (ht : t ≫ i = t') (hk : k ≫ i = k')
    (hc : HEq ((SSet.mapHomotopyCategory ((ihom X).map i)).map c) c')
    (hr : HEq ((SSet.mapHomotopyCategory ((ihom X).map i)).map r) r')
    (hq : HEq ((SSet.mapHomotopyCategory ((ihom X).map i)).map q) q')
    (hd : HEq ((SSet.mapHomotopyCategory ((ihom X).map i)).map d) d')
    (ha : HEq ((SSet.mapHomotopyCategory ((ihom X).map i)).map a) a')
    (he : c' ≫ r' = q' ≫ d' ≫ a') : c ≫ r = q ≫ d ≫ a := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_two_three_eq_of_heq
    ((SSet.mapHomotopyCategory ((ihom X).map i)).map c)
    ((SSet.mapHomotopyCategory ((ihom X).map i)).map r)
    ((SSet.mapHomotopyCategory ((ihom X).map i)).map q)
    ((SSet.mapHomotopyCategory ((ihom X).map i)).map d)
    ((SSet.mapHomotopyCategory ((ihom X).map i)).map a)
    c' r' q' d' a' hf hg hh ht hk hc hr hq hd ha he
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_injective_of_isFullyFaithful hi
  simpa only [CategoryTheory.Functor.map_comp] using! hh
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
