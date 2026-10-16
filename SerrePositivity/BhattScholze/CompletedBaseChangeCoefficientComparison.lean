module
public import SerrePositivity.BhattScholze.CompletedTensorPerfectoidization
public import SerrePositivity.BhattScholze.PerfectoidCompletedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeH0Coefficient

/-! # New-base coefficient comparison with a specified universal perfectoidization -/
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
local notation "A" => boundedAboveDerivedTensorAlgebra (R := R) S T
local notation "AC" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AC).X.obj

/-- The original universal map restricts to precisely the original left factor algebra map. -/
lemma completedTensorPerfectoidizationMap_left (s : S) :
    letI := derivedH0CommRing AC
    letI := derivedH0Algebra AC
    completedTensorPerfectoidizationMap R p S T (s ⊗ₜ[R] (1 : T)) =
      completedTensorH0LeftAlgHom R (p : R) S T s := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  let c : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
      (ModuleCat.of R S) s
  have hfac : derivedTensorH0AlgEquiv S T
      (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c) =
      s ⊗ₜ[R] (1 : T) := by
    change derivedTensorH0AlgHom S T
      (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c) = _
    rw [derivedTensorH0AlgHom_left]
    change (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R S) ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat R) 0).inv.app (ModuleCat.of R S) s)) = _
    rw [show (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R S) ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat R) 0).inv.app (ModuleCat.of R S) s) = s from
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
        (ModuleCat.of R S)).toLinearEquiv.apply_symm_apply s]
    rfl
  have he : (derivedTensorH0AlgEquiv S T).symm (s ⊗ₜ[R] (1 : T)) =
      derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c := by
    apply (derivedTensorH0AlgEquiv S T).injective
    rw [AlgEquiv.apply_symm_apply, hfac]
  rw [completedTensorPerfectoidizationMap_apply, completedTensorH0LeftAlgHom_apply,
    he, derivedH0AlgMap_comp_apply]
  rfl

variable [Fact p.Prime]

/-- Universal comparison is linear over the new base with its original specified algebra action. -/
lemma completedTensorPerfectoidizationMap_exists_algEquiv
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p)
    (D : Type u) [CommRing D] [Algebra S D] (f : S ⊗[R] T →ₐ[S] D)
    (hf : IsPerfectoidization p f.toRingHom) :
    letI := derivedH0CommRing AC
    letI := derivedH0Algebra AC
    letI := completedTensorH0LeftAlgebra R (p : R) S T
    ∃ e : H ≃ₐ[S] D,
      e.toRingHom.comp (completedTensorPerfectoidizationMap R p S T) = f.toRingHom := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) S T
  obtain ⟨e, he⟩ := completedTensorPerfectoidizationMap_exists_equiv R p S T
    hR hS hT D f.toRingHom hf
  have hc (s : S) : e (algebraMap S H s) = algebraMap S D s := by
    change e (completedTensorH0LeftAlgHom R (p : R) S T s) = _
    rw [← completedTensorPerfectoidizationMap_left]
    exact (RingHom.congr_fun he (s ⊗ₜ[R] (1 : T))).trans (f.commutes s)
  exact ⟨AlgEquiv.ofRingEquiv (f := e) hc, he⟩

/-- The original S-completed base-change coefficient is S-linearly equivalent to any
specified universal perfectoidization of the ordinary tensor. -/
lemma completedBaseChangeH0_exists_linearEquiv_perfectoidization
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p)
    (D : Type u) [CommRing D] [Algebra S D] (f : S ⊗[R] T →ₐ[S] D)
    (hf : IsPerfectoidization p f.toRingHom) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (algebraMap R S (p : R))).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj ≃ₗ[S] D) := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) S T
  obtain ⟨e, _he⟩ := completedTensorPerfectoidizationMap_exists_algEquiv R p S T
    hR hS hT D f hf
  exact ⟨(completedBaseChangeTensorH0LinearEquiv R S T (p : R)).trans e.toLinearEquiv⟩

/-- Original coefficient actions can be tested on ordinary new-base Tor with the
specified perfectoidization coefficient, retaining all power-torsion test modules. -/
lemma integralPerfectoid_torCoefficientScalar_eq_zero_iff_selectedPerfectoidizationTor
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R S)))
    (D : Type u) [CommRing D] [Algebra S D] (f : S ⊗[R] T →ₐ[S] D)
    (hf : IsPerfectoidization p f.toRingHom)
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (i : ℕ) (s : R) :
    torCoefficientScalarEndomorphism T N i (algebraMap R T s) = 0 ↔
      ∀ x : (((Tor (ModuleCat S) i).obj (ModuleCat.of S D)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj N)), algebraMap R S s • x = 0 := by
  obtain ⟨eh⟩ := completedBaseChangeH0_exists_linearEquiv_perfectoidization R p S T
    hR hS hT D f hf
  rw [map_natCast] at eh
  let M := (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
    ((boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj
  let L := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let eM : M ≅ ModuleCat.of S D := eh.toModuleIso
  let e := ((Tor (ModuleCat S) i).mapIso eM).app L
  apply (integralPerfectoid_torCoefficientScalar_eq_zero_iff_completedBaseChangeTor
    p R S T hR hS hT hflat N k hN i s).trans
  constructor
  · intro h z
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective z
    rw [← e.toLinearEquiv.map_smul, h, map_zero]
  · intro h x
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.map_smul, h, map_zero]

end SerrePositivity.BhattScholze
