module

public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensorPerfectoidization

/-! # Perfectoid tests of the original completed tensor H⁰

Use the existing G2 principal-completion comparison and its universal property.
No discreteness of the original tensor, bounded torsion, or classical-completion
comparison is assumed. This is the ring-valued part needed for BS Prop. 8.13.
-/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "C" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (C).X.obj

/-- Every map from the ordinary tensor to a perfectoid ring extends uniquely
over the actual H⁰ completion unit, including for unbounded p-power torsion. -/
lemma existsUnique_completedTensorPerfectoidLift
    (D : Type u) [CommRing D] (hD : IsIntegralPerfectoid D p) (f : S ⊗[R] T →+* D) :
    letI := derivedH0CommRing C
    ∃! g : H →+* D, g.comp (completedTensorPerfectoidizationMap R p S T) = f := by
  let := derivedH0CommRing C
  let := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  let e := completedTensorH0PrincipalRingEquiv R p S T
  have hc : letI := f.toAlgebra
      IsModuleComplete (S ⊗[R] T) (p : S ⊗[R] T) (ModuleCat.of (S ⊗[R] T) D) := by
    let := f.toAlgebra
    exact hD.isModuleComplete_algebra (S ⊗[R] T) D p
  obtain ⟨g, hg, huniq⟩ := principalCompletion_existsUnique_ringHom
    (S ⊗[R] T) (p : S ⊗[R] T) D f hc
  refine ⟨g.comp e.toRingHom, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    change g (e (e.symm (principalCompletionUnitRingHom (S ⊗[R] T) _ x))) = f x
    rw [e.apply_symm_apply]
    exact RingHom.congr_fun hg x
  · intro l hl
    have he : l.comp e.symm.toRingHom = g := huniq _ hl
    ext x
    have hx := RingHom.congr_fun he (e x)
    change l (e.symm (e x)) = g (e x) at hx
    change l x = g (e x)
    simpa only [e.symm_apply_apply] using hx

/-- Maps from the original completed tensor H⁰ to a perfectoid ring are
determined by their composition with the original ordinary-tensor unit. -/
lemma completedTensorPerfectoid_hom_ext
    (D : Type u) [CommRing D] (hD : IsIntegralPerfectoid D p) :
    letI := derivedH0CommRing C
    ∀ f g : H →+* D,
      f.comp (completedTensorPerfectoidizationMap R p S T) =
        g.comp (completedTensorPerfectoidizationMap R p S T) → f = g := by
  let := derivedH0CommRing C
  intro f g hfg
  exact (existsUnique_completedTensorPerfectoidLift R p S T D hD
    (f.comp (completedTensorPerfectoidizationMap R p S T))).unique rfl hfg.symm

/-- The specified map is extended over the same actual H⁰ completion unit. -/
def completedTensorPerfectoidLift
    (D : Type u) [CommRing D] (hD : IsIntegralPerfectoid D p) (f : S ⊗[R] T →+* D) :
    letI := derivedH0CommRing C
    H →+* D :=
  (existsUnique_completedTensorPerfectoidLift R p S T D hD f).choose

/-- The extension retains its specified original-tensor map. -/
lemma completedTensorPerfectoidLift_comp
    (D : Type u) [CommRing D] (hD : IsIntegralPerfectoid D p) (f : S ⊗[R] T →+* D) :
    letI := derivedH0CommRing C
    (completedTensorPerfectoidLift R p S T D hD f).comp
      (completedTensorPerfectoidizationMap R p S T) = f :=
  (existsUnique_completedTensorPerfectoidLift R p S T D hD f).choose_spec.1

/-- A ring-perfectoidization of the ordinary tensor is also one of the actual
completed tensor H⁰, via the extension of the very same unit. -/
lemma completedTensorPerfectoidLift_isPerfectoidization
    (D : Type u) [CommRing D] (f : S ⊗[R] T →+* D) (hf : IsPerfectoidization p f) :
    letI := derivedH0CommRing C
    IsPerfectoidization p (completedTensorPerfectoidLift R p S T D hf.1 f) := by
  let := derivedH0CommRing C
  refine ⟨hf.1, ?_⟩
  intro U _ hU k
  obtain ⟨l, hl, huniq⟩ := hf.2 U hU
    (k.comp (completedTensorPerfectoidizationMap R p S T))
  refine ⟨l, ?_, ?_⟩
  · apply completedTensorPerfectoid_hom_ext R p S T U hU
    rw [RingHom.comp_assoc, completedTensorPerfectoidLift_comp, hl]
  · intro m hm
    apply huniq
    rw [← completedTensorPerfectoidLift_comp R p S T D hf.1 f,
      ← RingHom.comp_assoc, hm]

end SerrePositivity.BhattScholze
