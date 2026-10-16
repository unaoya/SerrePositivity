module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Transport an equivariant short exact sequence to actual algebra modules -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- A base-linear morphism commuting with every actual C-scalar is C-linear. -/
def algebraLinearMapOfScalarCommutation {X Y : ModuleCat.{u} C}
    (f : (ModuleCat.restrictScalars (algebraMap R C)).obj X ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj Y)
    (h : ∀ c : C, (ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 X) ≫ f = f ≫ (ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 Y)) : X ⟶ Y :=
  ModuleCat.ofHom
    { toFun := f
      map_add' := f.hom.map_add
      map_smul' := fun c x => congrArg (fun g => g.hom x) (h c) }

lemma algebraConjugateMap_scalar_commutation
    {P Q : ModuleCat.{u} R} {X Y : ModuleCat.{u} C} (f : P ⟶ Q)
    (e : P ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj X) (d : Q ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj Y)
    (α : C → (P ⟶ P)) (β : C → (Q ⟶ Q))
    (hf : ∀ c, α c ≫ f = f ≫ β c)
    (he : ∀ c, α c ≫ e.hom = e.hom ≫ (ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 X))
    (hd : ∀ c, β c ≫ d.hom = d.hom ≫ (ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 Y)) (c : C) :
    (ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 X) ≫ (e.inv ≫ f ≫ d.hom) =
      (e.inv ≫ f ≫ d.hom) ≫ (ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 Y) := by
  have hi : (ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 X) ≫ e.inv = e.inv ≫ α c := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hi, Category.assoc, ← Category.assoc (α c), hf,
    Category.assoc, hd]
  simp only [Category.assoc]

variable (S : ShortComplex (ModuleCat.{u} R)) (X Y Z : ModuleCat.{u} C)
  (e₁ : S.X₁ ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj X) (e₂ : S.X₂ ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj Y) (e₃ : S.X₃ ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj Z)
  (α : C → (S ⟶ S))
  (h₁ : ∀ c, (α c).τ₁ ≫ e₁.hom = e₁.hom ≫ (ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 X))
  (h₂ : ∀ c, (α c).τ₂ ≫ e₂.hom = e₂.hom ≫ (ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 Y))
  (h₃ : ∀ c, (α c).τ₃ ≫ e₃.hom = e₃.hom ≫ (ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 Z))

/-- The original sequence, with its three actual coefficient-algebra modules. -/
def algebraEquivariantShortComplex : ShortComplex (ModuleCat.{u} C) :=
  ShortComplex.mk
    (algebraLinearMapOfScalarCommutation (e₁.inv ≫ S.f ≫ e₂.hom)
      (algebraConjugateMap_scalar_commutation S.f e₁ e₂
        (fun c => (α c).τ₁) (fun c => (α c).τ₂) (fun c => (α c).comm₁₂) h₁ h₂))
    (algebraLinearMapOfScalarCommutation (e₂.inv ≫ S.g ≫ e₃.hom)
      (algebraConjugateMap_scalar_commutation S.g e₂ e₃
        (fun c => (α c).τ₂) (fun c => (α c).τ₃) (fun c => (α c).comm₂₃) h₂ h₃))
    (by
      apply (ModuleCat.restrictScalars (algebraMap R C)).map_injective
      rw [Functor.map_comp, Functor.map_zero]
      change (e₁.inv ≫ S.f ≫ e₂.hom) ≫ (e₂.inv ≫ S.g ≫ e₃.hom) = 0
      simp only [Category.assoc, Iso.hom_inv_id_assoc, S.zero_assoc, zero_comp, comp_zero])

/-- Coefficient restriction recovers the original short complex, with all three specified isomorphisms. -/
def algebraEquivariantShortComplex_restrictIso :
    S ≅ (algebraEquivariantShortComplex S X Y Z e₁ e₂ e₃ α h₁ h₂ h₃).map (ModuleCat.restrictScalars (algebraMap R C)) :=
  ShortComplex.isoMk e₁ e₂ e₃
    (by change e₁.hom ≫ (e₁.inv ≫ S.f ≫ e₂.hom) = _; simp only [Iso.hom_inv_id_assoc])
    (by change e₂.hom ≫ (e₂.inv ≫ S.g ≫ e₃.hom) = _; simp only [Iso.hom_inv_id_assoc])

lemma algebraEquivariantShortComplex_shortExact (hS : S.ShortExact) :
    (algebraEquivariantShortComplex S X Y Z e₁ e₂ e₃ α h₁ h₂ h₃).ShortExact := by
  have hU := ShortComplex.shortExact_of_iso
    (algebraEquivariantShortComplex_restrictIso S X Y Z e₁ e₂ e₃ α h₁ h₂ h₃) hS
  let T := algebraEquivariantShortComplex S X Y Z e₁ e₂ e₃ α h₁ h₂ h₃
  let U := ModuleCat.restrictScalars (algebraMap R C)
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    exact (ShortComplex.moduleCat_exact_iff (T.map U)).mp hU.exact
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact (ModuleCat.mono_iff_injective (U.map T.f)).mp hU.mono_f
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact (ModuleCat.epi_iff_surjective (U.map T.g)).mp hU.epi_g

end SerrePositivity
