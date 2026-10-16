module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTorComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerHolimNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorMapZero

/-! # Power-torsion Tor tests supply the original ordinary-quotient tower actions -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)
  (S : Type u) [CommRing S] [Algebra R S]

/-- Standard power-torsion Tor tests kill the original tensor-stage action. -/
lemma modulePowerTensor_scalar_zero_of_power_torsion_tests (i : ℕ) (c : S)
    (h : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N i c = 0) (n : ℕ) :
    HomologicalComplex.homologyMap
      (((tensorLeft (modulePowerReduction a M n)).mapHomologicalComplex (.up ℤ)).map
        (extLift (projectiveResolution (ModuleCat.of R S))
          (ModuleCat.ofHom (LinearMap.mulLeft R c))
          (projectiveResolution (ModuleCat.of R S)))) (-(i : ℤ)) = 0 := by
  let K := extRes (projectiveResolution (ModuleCat.of R S))
  let f := extLift (projectiveResolution (ModuleCat.of R S))
    (ModuleCat.ofHom (LinearMap.mulLeft R c)) (projectiveResolution (ModuleCat.of R S))
  have he := modulePowerTensorModelIso_naturality a M f
    (moduleCoefficientResolution_flat (ModuleCat.of R S))
    (moduleCoefficientResolution_flat (ModuleCat.of R S)) n
  have hn := congrArg (fun f => HomologicalComplex.homologyMap f (-(i : ℤ))) he
  simp only [HomologicalComplex.homologyMap_comp] at hn
  have hz := modulePowerCokernel_scalar_zero_of_power_torsion_tests a M S i c h n
  rw [hz, zero_comp] at hn
  exact (cancel_epi (HomologicalComplex.homologyMap
    (modulePowerTensorModelIso a M K (moduleCoefficientResolution_flat (ModuleCat.of R S)) n).hom
    (-(i : ℤ)))).mp (by simpa using hn.symm)

/-- Adjacent standard Tor tests give zero composite of the original holim actions. -/
lemma modulePowerTensorHolim_homology_comp_zero_of_power_torsion_tests
    (i : ℕ) (c d : S)
    (hc : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N i c = 0)
    (hd : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N (i + 1) d = 0) :
    HomologicalComplex.homologyMap (modulePowerTensorHolimMap a M
      (extLift (projectiveResolution (ModuleCat.of R S))
        (ModuleCat.ofHom (LinearMap.mulLeft R c))
        (projectiveResolution (ModuleCat.of R S)))) (-(i : ℤ)) ≫
      HomologicalComplex.homologyMap (modulePowerTensorHolimMap a M
        (extLift (projectiveResolution (ModuleCat.of R S))
          (ModuleCat.ofHom (LinearMap.mulLeft R d))
          (projectiveResolution (ModuleCat.of R S)))) (-(i : ℤ)) = 0 := by
  apply complexTowerHomotopyLimitMap_homology_comp_eq_zero R
    (modulePowerTensorTransition a M _) (modulePowerTensorTransition a M _)
    _ (modulePowerTensorTransition_naturality a M _) _ _
    (modulePowerTensorTransition_naturality a M _)
  · exact modulePowerTensor_scalar_zero_of_power_torsion_tests a M S i c hc
  · intro n
    have hi : -(i : ℤ) - 1 = -((i + 1 : ℕ) : ℤ) := by omega
    rw [hi]
    exact modulePowerTensor_scalar_zero_of_power_torsion_tests a M S (i + 1) d hd n

attribute [local instance] HasDerivedCategory.standard

/-- Transfer a zero composite from cochain homology to its original derived image. -/
lemma derivedHomologyMap_comp_eq_zero_of_homologyMap_comp_eq_zero
    {K L P : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (g : L ⟶ P) (j : ℤ)
    (h : HomologicalComplex.homologyMap f j ≫ HomologicalComplex.homologyMap g j = 0) :
    (DerivedCategory.homologyFunctor (ModuleCat R) j).map (DerivedCategory.Q.map f) ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) j).map (DerivedCategory.Q.map g) = 0 := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R) j
  have hn := (DerivedCategory.homologyFunctorFactors (ModuleCat R) j).hom.naturality (f ≫ g)
  change H.map (DerivedCategory.Q.map (f ≫ g)) ≫ _ =
    _ ≫ HomologicalComplex.homologyMap (f ≫ g) j at hn
  rw [HomologicalComplex.homologyMap_comp, h, comp_zero] at hn
  rw [← H.map_comp, ← DerivedCategory.Q.map_comp]
  exact (cancel_mono ((DerivedCategory.homologyFunctorFactors (ModuleCat R) j).hom.app P)).mp
    (by simpa using hn)

/-- On the original actual derived tensor, adjacent power-torsion tests give a
zero composite of the original two coefficient actions. -/
lemma finiteCoefficientDerivedTensor_homology_comp_zero_of_power_torsion_tests
    [IsRegularLocalRing R] [Module.Finite R M]
    (hS : IsModuleComplete R a (ModuleCat.of R S)) (i : ℕ) (c d : S)
    (hc : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N i c = 0)
    (hd : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N (i + 1) d = 0) :
    let H := DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))
    H.map ((boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R c)))
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom) ≫
    H.map ((boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R d)))
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom) = 0 := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))
  let C := ModuleCat.of R S
  let fc : C ⟶ C := ModuleCat.ofHom (LinearMap.mulLeft R c)
  let fd : C ⟶ C := ModuleCat.ofHom (LinearMap.mulLeft R d)
  have hn₁ := congrArg H.map (finiteCoefficientPowerHolimIso_naturality_left a M fc hS hS)
  have hn₂ := congrArg H.map (finiteCoefficientPowerHolimIso_naturality_left a M fd hS hS)
  simp only [Functor.map_comp] at hn₁ hn₂
  have hz := derivedHomologyMap_comp_eq_zero_of_homologyMap_comp_eq_zero (R := R)
    (modulePowerTensorHolimMap a M (extLift (projectiveResolution C) fc (projectiveResolution C)))
    (modulePowerTensorHolimMap a M (extLift (projectiveResolution C) fd (projectiveResolution C)))
    (-(i : ℤ)) (modulePowerTensorHolim_homology_comp_zero_of_power_torsion_tests a M S i c d hc hd)
  change H.map (modulePowerDerivedTensorHolimMap a M fc) ≫
    H.map (modulePowerDerivedTensorHolimMap a M fd) = 0 at hz
  apply (cancel_mono (H.map (finiteCoefficientPowerHolimIso R a C M hS).hom)).mp
  rw [zero_comp, Category.assoc, hn₂, ← Category.assoc, hn₁, Category.assoc, hz, comp_zero]

/-- The zero composite holds on the existing standard Tor objects, not merely
on a selected cochain model. -/
lemma finiteCoefficientTor_comp_zero_of_power_torsion_tests
    [IsRegularLocalRing R] [Module.Finite R M]
    (hS : IsModuleComplete R a (ModuleCat.of R S)) (i : ℕ) (c d : S)
    (hc : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N i c = 0)
    (hd : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N (i + 1) d = 0) :
    torCoefficientScalarEndomorphism S M i c ≫ torCoefficientScalarEndomorphism S M i d = 0 := by
  let C := ModuleCat.of R S
  let H := DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))
  let e := (boundedAboveDerivedTensorModuleTorNatIso C i).app M
  have hn₁ := boundedAboveDerivedTensorModuleTorIso_naturality_left
    (ModuleCat.ofHom (LinearMap.mulLeft R c)) M i
  have hn₂ := boundedAboveDerivedTensorModuleTorIso_naturality_left
    (ModuleCat.ofHom (LinearMap.mulLeft R d)) M i
  change H.map _ ≫ e.hom = e.hom ≫ torCoefficientScalarEndomorphism S M i c at hn₁
  change H.map _ ≫ e.hom = e.hom ≫ torCoefficientScalarEndomorphism S M i d at hn₂
  have hz := finiteCoefficientDerivedTensor_homology_comp_zero_of_power_torsion_tests
    a M S hS i c d hc hd
  apply (cancel_epi e.hom).mp
  rw [comp_zero, ← Category.assoc, ← hn₁, Category.assoc, ← hn₂, ← Category.assoc, hz, zero_comp]

/-- Products of two tested coefficient elements annihilate standard Tor with finite M. -/
lemma finiteCoefficientTor_mul_zero_of_power_torsion_tests
    [IsRegularLocalRing R] [Module.Finite R M]
    (hS : IsModuleComplete R a (ModuleCat.of R S)) (i : ℕ) (c d : S)
    (hc : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N i c = 0)
    (hd : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
      (∀ x : N, a ^ k • x = 0) → torCoefficientScalarEndomorphism S N (i + 1) d = 0) :
    torCoefficientScalarEndomorphism S M i (c * d) = 0 := by
  have hmul : ModuleCat.ofHom (LinearMap.mulLeft R (c * d)) =
      ModuleCat.ofHom (LinearMap.mulLeft R c) ≫ ModuleCat.ofHom (LinearMap.mulLeft R d) := by
    ext x
    simp [mul_assoc, mul_comm, mul_left_comm]
  change ((Tor (ModuleCat.{u} R) i).flip.obj M).map
    (ModuleCat.ofHom (LinearMap.mulLeft R (c * d))) = 0
  rw [hmul, Functor.map_comp]
  exact finiteCoefficientTor_comp_zero_of_power_torsion_tests a M S hS i c d hc hd

end SerrePositivity.DerivedCompletion
