module
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulIsoRecovery
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskerExchange
/-!
概要：完全充満な後合成から、任意の全関手射を回収する。
方針：元の全関手圏の h における Hom 全単射を使う。
規約：射の可逆性は不要。使われ方：K-flat 双加群射の作用。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def fullyFaithfulPreimageFunctorHom {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsFullyFaithful f)
    {F G : K ⟶ X} (e : FunctorHom (F ≫ f) (G ≫ f)) : FunctorHom F G :=
  (hf.postcompose K).toHoFullyFaithful.preimage e
lemma fullyFaithfulPreimageFunctorHom_postcomp {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsFullyFaithful f)
    {F G : K ⟶ X} (e : FunctorHom (F ≫ f) (G ≫ f)) :
    (SSet.mapHomotopyCategory ((ihom K).map f)).map
      (fullyFaithfulPreimageFunctorHom hf e) = e := by
  exact (hf.postcompose K).toHoFullyFaithful.map_preimage
    (X := SSet.HomotopyCategory.mk (functorVertex F))
    (Y := SSet.HomotopyCategory.mk (functorVertex G)) e
lemma fullyFaithfulPreimageFunctorHom_iso_hom {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsFullyFaithful f)
    {F G : K ⟶ X} (e : FunctorIso (F ≫ f) (G ≫ f)) :
    fullyFaithfulPreimageFunctorHom hf e.hom = (hf.preimageFunctorIso e).hom := by
  rfl
end
end SerrePositivity.InfinityCategories
