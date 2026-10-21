module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskerExchange
/-!
概要：指定入力同型と全単体ホモトピーの交換を、同じ非可逆全関手射で扱う。
方針：指定された同じ比較と端点等式を保って全関手射を比較する。
規約：元の指定同型を変更しない。使われ方：実 augmentation と入力比較の正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
/-- 指定入力同型と元の出力ホモトピーは、同じ全関手射の交換正方形を満たす。 -/
lemma iso_precomp_homotopy_exchange {X Y Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z]
    {f₀ f₁ : X ⟶ Y} (e : FunctorIso f₀ f₁)
    {g₀ g₁ : Y ⟶ Z} (H : SSet.Homotopy g₀ g₁) :
    (e.postcomp g₀).hom ≫ Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H f₁)) =
    Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H f₀)) ≫
        (e.postcomp g₁).hom := by
  simp only [F2.functorIso_postcomp_hom, functorHomotopyPrecomp_hom]
  exact functorHom_whisker_exchange e.hom
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))
/-- 明示した三端点と指定射の一致は、非可逆な全関手射の合成にも保たれる。 -/
lemma functorHom_comp_heq {X Y : SSet.{u}} {f g h f' g' h' : X ⟶ Y}
    (e : FunctorHom f g) (d : FunctorHom g h)
    (e' : FunctorHom f' g') (d' : FunctorHom g' h')
    (hf : f = f') (hg : g = g') (hh : h = h')
    (he : HEq e e') (hd : HEq d d') : HEq (e ≫ d) (e' ≫ d') := by
  subst f' g' h'
  cases eq_of_heq he
  cases eq_of_heq hd
  rfl
end SerrePositivity.InfinityCategories
