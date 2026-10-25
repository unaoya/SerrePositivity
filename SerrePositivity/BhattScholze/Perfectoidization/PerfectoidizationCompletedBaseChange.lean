module
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedBaseChangeCoefficientComparison
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor

/-! # Original perfectoidization coefficients after completed base change -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (S A C : Type u)
    [CommRing S] [CommRing A] [CommRing C] [Algebra R S] [Algebra R A] [Algebra R C]
local notation "AC" => boundedAboveCompletedTensorAlgebra R (p : R) S C
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AC).X.obj

/-- The ordinary base change of the original perfectoidization map, followed by
the actual completed tensor unit, retaining the new base as the left factor. -/
def perfectoidizationCompletedBaseChangeMap (f : A →ₐ[R] C) :
    letI := derivedH0CommRing AC
    S ⊗[R] A →+* H := by
  letI := derivedH0CommRing AC
  exact (completedTensorPerfectoidizationMap R p S C).comp
    (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom

lemma perfectoidizationCompletedBaseChangeMap_left (f : A →ₐ[R] C) (s : S) :
    letI := derivedH0CommRing AC
    letI := derivedH0Algebra AC
    perfectoidizationCompletedBaseChangeMap R p S A C f (s ⊗ₜ[R] (1 : A)) =
      completedTensorH0LeftAlgHom R (p : R) S C s := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  change completedTensorPerfectoidizationMap R p S C (s ⊗ₜ[R] f 1) = _
  rw [map_one, completedTensorPerfectoidizationMap_left]

variable [Fact p.Prime]

/-- The same original base-change map is a universal perfectoidization. -/
lemma perfectoidizationCompletedBaseChangeMap_isPerfectoidization
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    letI := derivedH0CommRing AC
    IsPerfectoidization p (perfectoidizationCompletedBaseChangeMap R p S A C f) := by
  letI := derivedH0CommRing AC
  have hF := (completedTensorPerfectoidizationMap_isPerfectoidization
    R p S C hR hS hf.1).precomp_ringEquiv (Algebra.TensorProduct.comm R C S).toRingEquiv
  have hG := (perfectoidizationTensorBaseChangeMap_isPerfectoidization p f hf _ hF).precomp_ringEquiv
    (Algebra.TensorProduct.comm R S A).toRingEquiv
  convert hG using 1
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Comparison with the perfectoidization of the original base-changed algebra
preserves the new base action and the original base-changed unit. -/
lemma perfectoidizationCompletedBaseChangeMap_exists_algEquiv
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (D : Type u) [CommRing D] [Algebra S D] (g : S ⊗[R] A →ₐ[S] D)
    (hg : IsPerfectoidization p g.toRingHom) :
    letI := derivedH0CommRing AC
    letI := derivedH0Algebra AC
    letI := completedTensorH0LeftAlgebra R (p : R) S C
    ∃ e : H ≃ₐ[S] D,
      e.toRingHom.comp (perfectoidizationCompletedBaseChangeMap R p S A C f) =
        g.toRingHom := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) S C
  obtain ⟨e, he⟩ := (perfectoidizationCompletedBaseChangeMap_isPerfectoidization
    R p S A C hR hS f hf).exists_equiv p hg
  have hc (s : S) : e (algebraMap S H s) = algebraMap S D s := by
    change e (completedTensorH0LeftAlgHom R (p : R) S C s) = _
    rw [← perfectoidizationCompletedBaseChangeMap_left R p S A C f s]
    exact (RingHom.congr_fun he (s ⊗ₜ[R] (1 : A))).trans (g.commutes s)
  exact ⟨AlgEquiv.ofRingEquiv (f := e) hc, he⟩

/-- Original completed scalar extension of C has the original new-base module of
any specified perfectoidization of the base change of A. -/
lemma perfectoidizationCompletedBaseChange_exists_linearEquiv
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (D : Type u) [CommRing D] [Algebra S D] (g : S ⊗[R] A →ₐ[S] D)
    (hg : IsPerfectoidization p g.toRingHom) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (p : S)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))).obj ≃ₗ[S] D) := by
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI := completedTensorH0LeftAlgebra R (p : R) S C
  obtain ⟨e, _he⟩ := perfectoidizationCompletedBaseChangeMap_exists_algEquiv
    R p S A C hR hS f hf D g hg
  have eH := completedBaseChangeTensorH0LinearEquiv R S C (p : R)
  rw [map_natCast] at eH
  exact ⟨eH.trans e.toLinearEquiv⟩

/-- Original C-coefficient Tor is detected by the specified perfectoidization of
the base-changed original algebra A, with the original new-base scalar action. -/
lemma perfectoidization_torCoefficientScalar_eq_zero_iff_baseChangedPerfectoidizationTor
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R S)))
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (D : Type u) [CommRing D] [Algebra S D] (g : S ⊗[R] A →ₐ[S] D)
    (hg : IsPerfectoidization p g.toRingHom)
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (i : ℕ) (s : R) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
      ∀ x : (((Tor (ModuleCat S) i).obj (ModuleCat.of S D)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj N)), algebraMap R S s • x = 0 := by
  obtain ⟨eh⟩ := perfectoidizationCompletedBaseChange_exists_linearEquiv
    R p S A C hR hS f hf D g hg
  let M := (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
    ((boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))).obj
  let L := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let eM : M ≅ ModuleCat.of S D := eh.toModuleIso
  let e := ((Tor (ModuleCat S) i).mapIso eM).app L
  apply (integralPerfectoid_torCoefficientScalar_eq_zero_iff_completedBaseChangeTor
    p R S C hR hS hf.1 hflat N k hN i s).trans
  constructor
  · intro h z
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective z
    rw [← e.toLinearEquiv.map_smul, h, map_zero]
  · intro h x
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.map_smul, h, map_zero]

end SerrePositivity.BhattScholze
