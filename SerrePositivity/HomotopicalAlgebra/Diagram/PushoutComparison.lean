module

public import SerrePositivity.HomotopicalAlgebra.Quillen.LeftProper

/-! # Weak equivalences between arbitrary pushout cocones

The result applies to actual colimit cocones as well as the chosen pushout
objects. Both are compared by their canonical arrow isomorphism.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

lemma weakEquivalence_of_pushout_comparison
    {A B D P A' B' D' P' : C}
    {f : A ⟶ B} {g : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P}
    {f' : A' ⟶ B'} {g' : A' ⟶ D'} {l' : B' ⟶ P'} {r' : D' ⟶ P'}
    (s : IsPushout f g l r) (t : IsPushout f' g' l' r')
    (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D') (z : P ⟶ P')
    (hf : cofibrations C f) (hf' : cofibrations C f')
    (ha : weakEquivalences C a) (hb : weakEquivalences C b) (hc : weakEquivalences C c)
    (ef : f ≫ b = a ≫ f') (eg : g ≫ c = a ≫ g')
    (el : l ≫ z = b ≫ l') (er : r ≫ z = c ≫ r') : weakEquivalences C z := by
  let q := pushout.map f g f' g' b c a ef eg
  have hq := Quillen.pushout_map_weakEquivalence f g f' g' a b c hf hf' ha hb hc ef eg
  have hw : s.isoPushout.hom ≫ q = z ≫ t.isoPushout.hom := by
    apply s.hom_ext
    · calc
        l ≫ (s.isoPushout.hom ≫ q) = pushout.inl f g ≫ q := s.inl_isoPushout_hom_assoc q
        _ = b ≫ pushout.inl f' g' := pushout.inl_desc _ _ _
        _ = b ≫ (l' ≫ t.isoPushout.hom) := congrArg (fun k => b ≫ k) t.inl_isoPushout_hom.symm
        _ = (b ≫ l') ≫ t.isoPushout.hom := (Category.assoc _ _ _).symm
        _ = (l ≫ z) ≫ t.isoPushout.hom := congrArg (fun k => k ≫ t.isoPushout.hom) el.symm
        _ = l ≫ (z ≫ t.isoPushout.hom) := Category.assoc _ _ _
    · calc
        r ≫ (s.isoPushout.hom ≫ q) = pushout.inr f g ≫ q := s.inr_isoPushout_hom_assoc q
        _ = c ≫ pushout.inr f' g' := pushout.inr_desc _ _ _
        _ = c ≫ (r' ≫ t.isoPushout.hom) := congrArg (fun k => c ≫ k) t.inr_isoPushout_hom.symm
        _ = (c ≫ r') ≫ t.isoPushout.hom := (Category.assoc _ _ _).symm
        _ = (r ≫ z) ≫ t.isoPushout.hom := congrArg (fun k => k ≫ t.isoPushout.hom) er.symm
        _ = r ≫ (z ≫ t.isoPushout.hom) := Category.assoc _ _ _
  exact ((weakEquivalences C).arrow_iso_iff
    (Arrow.isoMk s.isoPushout t.isoPushout hw : Arrow.mk z ≅ Arrow.mk q)).mpr hq

end SerrePositivity.DiagramModel
