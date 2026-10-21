module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedMapBridges
public import SerrePositivity.InfinityCategories.Derived.FunctorHomLiftedPathReflection
/-!
概要：実包含後の比較と経路の反映を、同じ型付き全関手射で扱う。
方針：一般の関手空間で前後合成を回収し、元の指定値を保つ。
規約：可逆性は追加しない。使われ方：K-flat 合成比較の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorHom_two_three_reflect_typed_precomp {X Y X' Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z] (i : Y ⟶ Z) (hi : IsFullyFaithful i) (J : X ⟶ X')
    {f g h t k : X ⟶ Y} {f' g' h' t' k' : X' ⟶ Z}
    (c : FunctorHom f g) (r : FunctorHom g k)
    (q : FunctorHom f h) (d : FunctorHom h t) (a : FunctorHom t k)
    (c' : FunctorHom f' g') (r' : FunctorHom g' k')
    (q' : FunctorHom f' h') (d' : FunctorHom h' t') (a' : FunctorHom t' k')
    (hf : f ≫ i = J ≫ f') (hg : g ≫ i = J ≫ g') (hh : h ≫ i = J ≫ h')
    (ht : t ≫ i = J ≫ t') (hk : k ≫ i = J ≫ k')
    (hc : HEq (functorHomPostcomp f g i c) (functorHomPrecomp f' g' J c'))
    (hr : HEq (functorHomPostcomp g k i r) (functorHomPrecomp g' k' J r'))
    (hq : HEq (functorHomPostcomp f h i q) (functorHomPrecomp f' h' J q'))
    (hd : HEq (functorHomPostcomp h t i d) (functorHomPrecomp h' t' J d'))
    (ha : HEq (functorHomPostcomp t k i a) (functorHomPrecomp t' k' J a'))
    (he : c' ≫ r' = q' ≫ d' ≫ a') : c ≫ r = q ≫ d ≫ a := by
  have hp := congrArg (fun e => functorHomPrecomp f' k' J e) he
  have hp' : functorHomPrecomp f' g' J c' ≫ functorHomPrecomp g' k' J r' =
      functorHomPrecomp f' h' J q' ≫ functorHomPrecomp h' t' J d' ≫
        functorHomPrecomp t' k' J a' := by
    simpa only [functorHomPrecomp, CategoryTheory.Functor.map_comp] using! hp
  exact functorHom_two_three_reflect_postcomp i hi c r q d a
    (functorHomPrecomp f' g' J c') (functorHomPrecomp g' k' J r')
    (functorHomPrecomp f' h' J q') (functorHomPrecomp h' t' J d')
    (functorHomPrecomp t' k' J a') hf hg hh ht hk
    ((functorHomPostcomp_map_heq f g i c).symm.trans hc)
    ((functorHomPostcomp_map_heq g k i r).symm.trans hr)
    ((functorHomPostcomp_map_heq f h i q).symm.trans hq)
    ((functorHomPostcomp_map_heq h t i d).symm.trans hd)
    ((functorHomPostcomp_map_heq t k i a).symm.trans ha) hp'
end
end SerrePositivity.InfinityCategories
