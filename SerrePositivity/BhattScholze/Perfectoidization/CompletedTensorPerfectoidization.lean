module
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidCompletedTensorDiscrete
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationBaseChange
public import SerrePositivity.CommutativeAlgebra.PerfectoidDerivedComplete

/-! # The original completed tensor H⁰ is the universal perfectoid tensor

The unit is normalized by the original actual H⁰ completion unit. The target
retains precisely its original H⁰ ring structure, including zero factors.
-/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "ORIG" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ORIG).X.obj

/-- The ordinary tensor enters the actual completed H⁰ through the canonical unit comparison. -/
def completedTensorPerfectoidizationMap :
    letI := derivedH0CommRing ORIG
    S ⊗[R] T →+* H := by
  letI := derivedH0CommRing ORIG
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  exact (completedTensorH0PrincipalRingEquiv R p S T).symm.toRingHom.comp
    (principalCompletionUnitRingHom (S ⊗[R] T) (p : S ⊗[R] T))

/-- It is exactly the original H⁰ completion unit, on the standard ordinary tensor classes. -/
lemma completedTensorPerfectoidizationMap_apply (x : S ⊗[R] T) :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) S T)
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) S T)
    letI := derivedH0CommRing ORIG
    completedTensorPerfectoidizationMap R p S T x =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T))
        ((derivedTensorH0AlgEquiv S T).symm x) := by
  letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) S T)
  letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) S T)
  letI := derivedH0CommRing ORIG
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  apply (completedTensorH0PrincipalRingEquiv R p S T).injective
  change completedTensorH0PrincipalRingEquiv R p S T
    ((completedTensorH0PrincipalRingEquiv R p S T).symm _) = _
  rw [RingEquiv.apply_symm_apply, completedTensorH0PrincipalRingEquiv_unit,
    AlgEquiv.apply_symm_apply]

variable [Fact p.Prime]

/-- The same actual map is a perfectoidization; arbitrary perfectoid targets are p-complete. -/
lemma completedTensorPerfectoidizationMap_isPerfectoidization
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    letI := derivedH0CommRing ORIG
    IsPerfectoidization p (completedTensorPerfectoidizationMap R p S T) := by
  letI := derivedH0CommRing ORIG
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  let e := completedTensorH0PrincipalRingEquiv R p S T
  refine ⟨integralPerfectoid_completedTensorH0_isIntegralPerfectoid p R S T hR hS hT, ?_⟩
  intro D _ hD f
  have hc : letI := f.toAlgebra
      IsModuleComplete (S ⊗[R] T) (p : S ⊗[R] T) (ModuleCat.of (S ⊗[R] T) D) := by
    letI := f.toAlgebra
    exact hD.isModuleComplete_algebra (S ⊗[R] T) D p
  obtain ⟨g, hg, huniq⟩ := principalCompletion_existsUnique_ringHom
    (S ⊗[R] T) (p : S ⊗[R] T) D f hc
  refine ⟨g.comp e.toRingHom, ?_, ?_⟩
  · change (g.comp e.toRingHom).comp
      (e.symm.toRingHom.comp (principalCompletionUnitRingHom (S ⊗[R] T) _)) = f
    apply RingHom.ext
    intro x
    change g (e (e.symm (principalCompletionUnitRingHom (S ⊗[R] T) _ x))) = f x
    rw [e.apply_symm_apply]
    exact RingHom.congr_fun hg x
  · intro l hl
    have he : l.comp e.symm.toRingHom = g := by
      apply huniq
      exact hl
    ext x
    have hx := RingHom.congr_fun he (e x)
    change l (e.symm (e x)) = g (e x) at hx
    rw [e.symm_apply_apply] at hx
    exact hx

/-- Comparison with any selected universal perfectoid tensor retains its specified unit. -/
lemma completedTensorPerfectoidizationMap_exists_equiv
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p)
    (D : Type u) [CommRing D] (f : S ⊗[R] T →+* D) (hf : IsPerfectoidization p f) :
    letI := derivedH0CommRing ORIG
    ∃ e : H ≃+* D, e.toRingHom.comp (completedTensorPerfectoidizationMap R p S T) = f := by
  letI := derivedH0CommRing ORIG
  exact (completedTensorPerfectoidizationMap_isPerfectoidization R p S T hR hS hT).exists_equiv p hf

/-- Actual completed tensor H⁰ realizes perfectoidization after changing the base
of any specified universal perfectoidization map. -/
lemma completedTensorBaseChangeMap_isPerfectoidization
    (hR : IsIntegralPerfectoid R p) (hT : IsIntegralPerfectoid T p)
    (A : Type u) [CommRing A] [Algebra R A] (f : A →ₐ[R] S)
    (hf : IsPerfectoidization p f.toRingHom) :
    letI := derivedH0CommRing ORIG
    IsPerfectoidization p (perfectoidizationTensorBaseChangeMap f
      (completedTensorPerfectoidizationMap R p S T)) := by
  letI := derivedH0CommRing ORIG
  exact perfectoidizationTensorBaseChangeMap_isPerfectoidization p f hf _
    (completedTensorPerfectoidizationMap_isPerfectoidization R p S T hR hf.1 hT)

/-- The original actual H⁰ unit has the same mod-p bijectivity as the established
perfectoid tensor model, transported through a unit-preserving universal equivalence. -/
lemma completedTensorPerfectoidizationMap_modP_bijective
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    letI := derivedH0CommRing ORIG
    Function.Bijective (modPMap p (completedTensorPerfectoidizationMap R p S T)) := by
  letI := derivedH0CommRing ORIG
  obtain ⟨D, hD, F, hF, hbij⟩ :=
    exists_perfectoidTensorPerfectoidization_modP p R S T hR hS hT
  letI := hD
  obtain ⟨e, he⟩ := completedTensorPerfectoidizationMap_exists_equiv R p S T hR hS hT D F hF
  let ep : ModP H p ≃+* ModP D p := Ideal.quotientEquiv _ _ e
    (by simp only [Ideal.map_span, Set.image_singleton, map_natCast])
  have hep (x : ModP (S ⊗[R] T) p) :
      ep (modPMap p (completedTensorPerfectoidizationMap R p S T) x) = modPMap p F x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (e (completedTensorPerfectoidizationMap R p S T x)) =
      Ideal.Quotient.mk _ (F x)
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun he x)
  constructor
  · intro x y hxy
    apply hbij.1
    rw [← hep x, ← hep y, hxy]
  · intro z
    obtain ⟨x, hx⟩ := hbij.2 (ep z)
    refine ⟨x, ep.injective ?_⟩
    rw [hep x, hx]

end SerrePositivity.BhattScholze
