module
public import SerrePositivity.KST.SConstruction.DGHomGluingBimodule
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
/-!
概要：恒等脚に沿う制限 Yoneda と Hom gluing 係数を、全 dg 関手の等号で同定する。
方針：加群 Hom の全評価で対象移送と Hom 作用を照合し、厳密な合成単位則を使う。
規約：対象別同型や h 圏での比較へ弱めない。新しい公理と追加の完備性仮定は使わない。
使われ方：恒等二脚の導来 lax 模型を同じ Yoneda 二脚へ照合する入口。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
private lemma transport_pi {M N M' N' : RightModule R C} (hM : M = M') (hN : N = N')
    (c : C) :
    eqToHom (congrArg₂ (moduleHom R C) hM hN) ≫ moduleHomπ R C M' N' c =
      moduleHomπ R C M N c ≫ eqToHom
        (congrArg₂ (homObject R (Complex R))
          (congrArg (fun M : RightModule R C => M.obj (op c)) hM)
          (congrArg (fun M : RightModule R C => M.obj (op c)) hN)) := by
  cases hM
  cases hN
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
/-- 概要：恒等脚に制限した Yoneda は元の実 Yoneda に等しい。
方針：加群 Hom の全評価で対象移送を消す。規約：全次数の dg 関手等号。
使われ方：恒等 Hom 係数の厳密同定。 -/
lemma dgRestrictedYoneda_id :
    dgRestrictedYoneda R C C (DGFunctor.id C) = dgYoneda R C := by
  have ho (x : C) : (dgRestrictedYoneda R C C (DGFunctor.id C)).obj x =
      (dgYoneda R C).obj x := by
    change (DGFunctor.id C).op.comp (representable R x) = representable R x
    rw [DGFunctor.op_id]
    exact strictDGFunctor_id_comp _
  apply EnrichedFunctor.ext (Complex R) ho
  intro x y
  apply moduleHom_ext
  intro c
  change ((dgRestrictedYoneda R C C (DGFunctor.id C)).map x y ≫
    eqToHom (congrArg₂ (moduleHom R C) (ho x) (ho y))) ≫
      moduleHomπ R C (representable R x) (representable R y) c =
        yonedaHom R C x y ≫ moduleHomπ R C (representable R x) (representable R y) c
  have hπ := transport_pi R C (ho x) (ho y) c
  have hs := congrArg (fun f => (dgRestrictedYoneda R C C (DGFunctor.id C)).map x y ≫ f) hπ
  have ht := (Category.assoc
    ((dgRestrictedYoneda R C C (DGFunctor.id C)).map x y)
    (eqToHom (congrArg₂ (moduleHom R C) (ho x) (ho y)))
    (moduleHomπ R C (representable R x) (representable R y) c)).trans hs
  apply ht.trans
  change (dgRestrictedYoneda R C C (DGFunctor.id C)).map x y ≫
    (moduleHomπ R C _ _ c ≫ 𝟙 _) = _
  exact (congrArg
    (fun f => (dgRestrictedYoneda R C C (DGFunctor.id C)).map x y ≫ f)
    (Category.comp_id _)).trans
      ((dgRestrictedYoneda_map_π R C C (DGFunctor.id C) x y c).trans
        ((yonedaHom_π R C x y c).trans
          (SerrePositivity.DifferentialGraded.endomorphismYonedaApp R C c x y)).symm)
/-- 概要：左脚が恒等なら Hom gluing 係数は右脚後の Yoneda そのもの。
方針：制限 Yoneda の恒等式を代入する。規約：右脚の全 Hom 作用を保持。
使われ方：同じ角を持つ導来係数の照合。 -/
lemma dgHomGluingIdentityLeft_coefficient (D : Type w) [DGCategory R D]
    (q : DGFunctor R D C) :
    (dgHomGluingBimodule R C D C (DGFunctor.id C) q).toFunctor = q.comp (dgYoneda R C) := by
  change q.comp (dgRestrictedYoneda R C C (DGFunctor.id C)) = _
  rw [dgRestrictedYoneda_id]

/-- 概要：恒等二脚の実 Hom gluing 係数は元の dg Yoneda そのもの。
方針：左脚同定と厳密合成単位則を使う。規約：対象と全次数 Hom を保持。
使われ方：恒等 lax 差への全比較の係数入口。 -/
lemma dgHomGluingIdentity_coefficient :
    (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C)).toFunctor =
      dgYoneda R C :=
  (dgHomGluingIdentityLeft_coefficient R C C (DGFunctor.id C)).trans
    (strictDGFunctor_id_comp (dgYoneda R C))
end SerrePositivity.KST.SConstruction
