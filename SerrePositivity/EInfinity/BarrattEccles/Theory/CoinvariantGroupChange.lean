module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.Algebra.Homology.Additive

/-!
# 群の同型に沿う余不変の比較

HA 3.2.4.7 の自由比較で、安定化群と指定二色部分群の同定を余不変へ運ぶ。
商の生成元を変えず、表現の射と複体の微分に自然な同型を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Representation HomologicalComplex
variable {A G H : Type u} [CommRing A] [Group G] [Group H] (e : G ≃* H)

/-- 群の同型に沿う制限は、指定商の生成元を保つ余不変の同型を与える。 -/
def coinvariantGroupChangeIso (V : Rep.{u} A H) :
    (Rep.coinvariantsFunctor A G).obj (Rep.res e.toMonoidHom V) ≅
      (Rep.coinvariantsFunctor A H).obj V where
  hom := ModuleCat.ofHom (Coinvariants.lift _ (Coinvariants.mk V.ρ) (by
    intro g
    ext v
    exact Coinvariants.mk_self_apply V.ρ (e g) v))
  inv := ModuleCat.ofHom (Coinvariants.lift V.ρ
    (Coinvariants.mk (Rep.res e.toMonoidHom V).ρ) (by
    intro h
    ext v
    simpa using Coinvariants.mk_self_apply (Rep.res e.toMonoidHom V).ρ (e.symm h) v))
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply Coinvariants.hom_ext
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply Coinvariants.hom_ext
    rfl

/-- 制限後の余不変の生成元は、元の同じ生成元へ送られる。 -/
lemma coinvariantGroupChangeIso_hom_mk (V : Rep.{u} A H) (v : V) :
    (coinvariantGroupChangeIso e V).hom (Coinvariants.mk _ v) = Coinvariants.mk _ v := rfl

/-- 群変更の指定同型は、表現の射について自然である。 -/
lemma coinvariantGroupChangeIso_naturality {V W : Rep.{u} A H} (f : V ⟶ W) :
    (Rep.coinvariantsFunctor A G).map ((Rep.resFunctor e.toMonoidHom).map f) ≫
        (coinvariantGroupChangeIso e W).hom =
      (coinvariantGroupChangeIso e V).hom ≫ (Rep.coinvariantsFunctor A H).map f := by
  apply ModuleCat.hom_ext
  apply Coinvariants.hom_ext
  rfl

/-- 群変更は、余不変の関手全体の指定自然同型である。 -/
def coinvariantGroupChangeNatIso :
    Rep.resFunctor e.toMonoidHom ⋙ Rep.coinvariantsFunctor A G ≅
      Rep.coinvariantsFunctor A H :=
  NatIso.ofComponents (coinvariantGroupChangeIso e)
    (fun f => coinvariantGroupChangeIso_naturality e f)

/-- 任意の複体で、群変更と指定商写像は元の微分を保つ。 -/
def coinvariantGroupChangeComplexIso (K : CochainComplex (Rep.{u} A H) ℤ) :
    ((Rep.coinvariantsFunctor A G).mapHomologicalComplex (.up ℤ)).obj
      (((Rep.resFunctor e.toMonoidHom).mapHomologicalComplex (.up ℤ)).obj K) ≅
        ((Rep.coinvariantsFunctor A H).mapHomologicalComplex (.up ℤ)).obj K :=
  (Functor.mapHomologicalComplexCompIso
    (F := Rep.resFunctor e.toMonoidHom) (G := Rep.coinvariantsFunctor A G)
    (Iso.refl _) (.up ℤ)).app K ≪≫
      (NatIso.mapHomologicalComplex (coinvariantGroupChangeNatIso (A := A) e) (.up ℤ)).app K

end SerrePositivity.EInfinity
