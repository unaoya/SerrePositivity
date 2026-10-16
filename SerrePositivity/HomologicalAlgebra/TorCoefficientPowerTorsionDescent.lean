module
public import SerrePositivity.HomologicalAlgebra.PowerTorsionDerivedDescent
public import SerrePositivity.HomologicalAlgebra.DerivedTensorLinear
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison
public import SerrePositivity.HomologicalAlgebra.TorAlgebraScalarComparison

/-! # Faithful descent of the original Tor coefficient scalar on power-torsion tests -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R S C : Type u} [CommRing R] [CommRing S] [CommRing C] [Algebra R C]

/-- A scalar killing the right module kills its entire original actual derived tensor. -/
lemma derivedTensor_scalar_id_eq_zero_of_right_annihilates
    (M N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0) :
    a • 𝟙 (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)) = 0 := by
  let X := boundedAboveDerivedSingleFunctor.obj M
  let Y := boundedAboveDerivedSingleFunctor.obj N
  have hN : a • 𝟙 N = 0 := by ext x; exact ha x
  have hY : a • 𝟙 Y = 0 := by
    apply InducedCategory.hom_ext
    change a • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj N) = 0
    have h := congrArg (DerivedCategory.singleFunctor (ModuleCat R) 0).map hN
    simpa only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] using h
  change a • 𝟙 (X ⊗ Y) = 0
  calc
    a • 𝟙 (X ⊗ Y) = (𝟙 X) ⊗ₘ (a • 𝟙 Y) := by
      rw [derivedTensorHom_smul_right, id_tensorHom_id]
    _ = 0 := by rw [hY]; simp

/-- The same scalar kills all actual tensor homology modules, with the same exponent. -/
lemma derivedTensor_homology_annihilated_of_right_annihilates
    (M N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0) (i : ℤ) :
    ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)).obj,
      a • x = 0 := by
  let X := boundedAboveDerivedTensor.obj
    (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)
  have h : a • 𝟙 X.obj = 0 :=
    congrArg (fun f : X ⟶ X => f.hom)
      (derivedTensor_scalar_id_eq_zero_of_right_annihilates M N a ha)
  have hh := congrArg (DerivedCategory.homologyFunctor (ModuleCat R) i).map h
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at hh
  intro x
  exact congrArg (fun f => f.hom x) hh

/-- A coefficient scalar coming from the base ring is the original base scalar on ordinary Tor. -/
lemma torCoefficientScalar_algebraMap_eq_smul_id (N : ModuleCat.{u} R) (i : ℕ) (a : R) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C a) =
      a • 𝟙 (((Tor (ModuleCat R) i).obj (ModuleCat.of R C)).obj N) := by
  let U := ModuleCat.restrictScalars (algebraMap R C)
  let A := ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj N
  let e := torAlgebraComparison (C := C) N i
  have hu : U.map ((algebraMap R C a) • 𝟙 A) = a • 𝟙 (U.obj A) := by
    ext x
    rfl
  have h := torAlgebraComparison_coefficient_scalar N i (algebraMap R C a)
  apply (cancel_mono e.hom).mp
  calc
    _ = e.hom ≫ U.map ((algebraMap R C a) • 𝟙 A) := h
    _ = e.hom ≫ (a • 𝟙 (U.obj A)) := congrArg (fun f => e.hom ≫ f) hu
    _ = a • e.hom := by
      rw [Linear.comp_smul]
      exact congrArg (fun f => a • f) (Category.comp_id e.hom)
    _ = (a • 𝟙 _) ≫ e.hom := by simp

/-- Zero action agrees on the actual derived tensor homology and the original Tor. -/
lemma torCoefficientScalar_eq_zero_iff_derivedTensor_annihilated
    (N : ModuleCat.{u} R) (i : ℕ) (s : R) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C),
            boundedAboveDerivedSingleFunctor.obj N)).obj, s • x = 0 := by
  rw [torCoefficientScalar_algebraMap_eq_smul_id]
  let e := (boundedAboveDerivedTensorModuleTorNatIso (ModuleCat.of R C) i).app N
  constructor
  · intro h x
    apply e.toLinearEquiv.injective
    rw [map_smul, map_zero]
    exact congrArg (fun f => f.hom (e.hom x)) h
  · intro h
    ext z
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective z
    change s • e.hom x = 0
    rw [← e.hom.hom.map_smul, h x, map_zero]

/-- A completely faithfully flat extension detects the original scalar zero on all torsion Tor tests.
The derived base change of the original tensor is retained explicitly. -/
lemma torCoefficientScalar_eq_zero_iff_powerTorsion_baseChange
    (φ : R →+* S) (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, a ^ k • x = 0) (i : ℕ) (s : R) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) (-(i : ℤ))).obj
        ((boundedAboveDerivedBaseChange φ).obj
          (boundedAboveDerivedTensor.obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C),
              boundedAboveDerivedSingleFunctor.obj N))).obj, φ s • x = 0 := by
  exact (torCoefficientScalar_eq_zero_iff_derivedTensor_annihilated N i s).trans
    (powerTorsionDerivedHomology_annihilated_iff φ a hS k _
      (derivedTensor_homology_annihilated_of_right_annihilates (ModuleCat.of R C) N
        (a ^ k) hN) s (-(i : ℤ))).symm

end SerrePositivity
