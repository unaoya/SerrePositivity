module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra
/-!
概要：指定同型の逆と任意全関手射の共役式を、同じ入力前合成へ移送する。
方針：端点を明示して射の一致を保ち、前合成の関手性だけを使う。
規約：指定値を保持し射の可逆性を追加しない。使われ方：変更同型の公開式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
lemma functorIso_inv_heq_of_endpoint_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (e' : FunctorIso f' g') (hf : f = f') (hg : g = g')
    (he : HEq e e') : HEq e.inv e'.inv := by
  subst f' g'
  cases eq_of_heq he
  rfl
lemma functorHom_conjugation_precomp {X Y Z : SSet.{u}}
    {f g f' g' : X ⟶ Y} (c : FunctorIso f g) (p : FunctorIso f f')
    (q : FunctorIso g g') (a : FunctorHom f' g')
    (h : c.hom = p.hom ≫ a ≫ q.inv) (J : Z ⟶ X) :
    (c.precomp J).hom = (p.precomp J).hom ≫
      functorHomPrecomp f' g' J a ≫ (q.precomp J).inv := by
  have hh := congrArg (fun k => functorHomPrecomp f g J k) h
  simpa only [functorHomPrecomp_comp, functorIso_precomp_hom_typed] using! hh
end SerrePositivity.InfinityCategories
