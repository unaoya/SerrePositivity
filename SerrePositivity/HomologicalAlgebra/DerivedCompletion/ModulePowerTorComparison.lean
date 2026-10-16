module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerDerivedComparison
public import SerrePositivity.HomologicalAlgebra.DerivedTensorTorNaturality
public import SerrePositivity.HomologicalAlgebra.KoszulTorComparison

/-! # The actual power-cokernel tower and standard Tor coefficient actions -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (C M : ModuleCat.{u} R)

/-- The homology of the original power cokernel is the standard Tor module,
with C first and the ordinary M/aⁿM as the test module. -/
def modulePowerCokernelTorIso (n i : ℕ) :
    (powerCokernelComplex a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n).homology
        (-(i : ℤ)) ≅ ((Tor (ModuleCat R) i).obj C).obj (modulePowerReduction a M n) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).symm.app _ ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))).mapIso
      (modulePowerDerivedTensorIso a C M n) ≪≫
        (boundedAboveDerivedTensorModuleTorNatIso C i).app (modulePowerReduction a M n)

/-- The homology tower uses the standard Tor maps of the ordinary quotient
transitions, in every degree and including the zero-power stage. -/
@[reassoc] lemma modulePowerCokernelTorIso_transition (n i : ℕ) :
    homologyMap (powerCokernelComplexTransition a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n) (-(i : ℤ)) ≫
        (modulePowerCokernelTorIso a C M n i).hom =
      (modulePowerCokernelTorIso a C M (n + 1) i).hom ≫
        ((Tor (ModuleCat R) i).obj C).map (modulePowerReductionTransition a M n) := by
  let fk := powerCokernelComplexTransition a
    ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n
  let H := DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))
  have h₁ := (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).inv.naturality fk
  have h₂ := congrArg H.map (modulePowerDerivedTensorIso_transition a C M n)
  simp only [Functor.map_comp] at h₂
  have h₃ := (boundedAboveDerivedTensorModuleTorNatIso C i).hom.naturality
    (modulePowerReductionTransition a M n)
  dsimp only [fk, Functor.comp_map] at h₁
  change homologyMap (powerCokernelComplexTransition a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n) (-(i : ℤ)) ≫ _ =
    _ ≫ H.map (DerivedCategory.Q.map (powerCokernelComplexTransition a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n)) at h₁
  dsimp only [Functor.comp_map] at h₃
  simp only [modulePowerCokernelTorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, h₁, Category.assoc]
  rw [← Category.assoc (H.map (DerivedCategory.Q.map fk)), h₂]
  simp only [Category.assoc]
  rw [h₃]

variable {C} {D : ModuleCat.{u} R}

@[reassoc] lemma modulePowerCokernelTorIso_naturality (f : C ⟶ D) (n i : ℕ) :
    homologyMap (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution C) f (projectiveResolution D)) n) (-(i : ℤ)) ≫
        (modulePowerCokernelTorIso a D M n i).hom =
      (modulePowerCokernelTorIso a C M n i).hom ≫
        ((Tor (ModuleCat R) i).map f).app (modulePowerReduction a M n) := by
  let fk := modulePowerTensorCokernelMap a M
    (extLift (projectiveResolution C) f (projectiveResolution D)) n
  let H := DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))
  have h₁ := (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).inv.naturality fk
  have h₂ := congrArg H.map (modulePowerDerivedTensorIso_naturality a M f n)
  simp only [Functor.map_comp] at h₂
  have h₃ := boundedAboveDerivedTensorModuleTorIso_naturality_left f
    (modulePowerReduction a M n) i
  dsimp only [fk, Functor.comp_map] at h₁
  change homologyMap (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution C) f (projectiveResolution D)) n) (-(i : ℤ)) ≫ _ =
    _ ≫ H.map (DerivedCategory.Q.map (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution C) f (projectiveResolution D)) n)) at h₁
  simp only [modulePowerCokernelTorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, h₁, Category.assoc]
  rw [← Category.assoc (H.map (DerivedCategory.Q.map fk)), h₂]
  simp only [Category.assoc]
  rw [h₃]

/-- Zero scalar action is reflected and preserved by the actual Tor comparison. -/
lemma modulePowerCokernelTorIso_scalar_zero_iff
    (S : Type u) [CommRing S] [Algebra R S] (n i : ℕ) (s : S) :
    homologyMap (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution (ModuleCat.of R S))
        (ModuleCat.ofHom (LinearMap.mulLeft R s))
        (projectiveResolution (ModuleCat.of R S))) n) (-(i : ℤ)) = 0 ↔
      torCoefficientScalarEndomorphism S (modulePowerReduction a M n) i s = 0 := by
  let e := modulePowerCokernelTorIso a (ModuleCat.of R S) M n i
  have he := modulePowerCokernelTorIso_naturality a M
    (ModuleCat.ofHom (LinearMap.mulLeft R s)) n i
  change _ ≫ e.hom = e.hom ≫
    torCoefficientScalarEndomorphism S (modulePowerReduction a M n) i s at he
  constructor
  · intro h
    apply (cancel_epi e.hom).mp
    rw [comp_zero, ← he, h, zero_comp]
  · intro h
    apply (cancel_mono e.hom).mp
    rw [zero_comp, he, h, comp_zero]

/-- A Tor-annihilation input on power-torsion test modules supplies the actual
scalar zero map at every stage of the original cokernel tower. -/
lemma modulePowerCokernel_scalar_zero_of_power_torsion_tests
    (S : Type u) [CommRing S] [Algebra R S] (i : ℕ) (s : S)
    (h : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N i s = 0)
    (n : ℕ) :
    homologyMap (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution (ModuleCat.of R S))
        (ModuleCat.ofHom (LinearMap.mulLeft R s))
        (projectiveResolution (ModuleCat.of R S))) n) (-(i : ℤ)) = 0 := by
  apply (modulePowerCokernelTorIso_scalar_zero_iff a M S n i s).mpr
  apply h (modulePowerReduction a M n) (n + 1) (by omega)
  intro x
  rw [pow_succ', mul_smul, modulePowerReduction_pow_smul_zero, smul_zero]

end SerrePositivity.DerivedCompletion
