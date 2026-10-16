module
public import SerrePositivity.HomologicalAlgebra.TorCoefficientPowerTorsionDescent
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTensor
public import SerrePositivity.HomologicalAlgebra.ModuleScalarExtensionAnnihilator

/-! # Completed coefficient base change for original power-torsion Tor tests

Only the left coefficient is completed. The right module is the original
ordinary scalar extension, identified by the standard augmentation.
-/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)

/-- Complete flatness suffices to make arbitrary power-torsion modules Tor-acyclic. -/
lemma scalarExtensionTorVanishing_of_completelyFlat_powerTorsion
    (hS : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, a ^ k • x = 0) :
    scalarExtensionTorVanishing φ N := by
  intro i hi
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (torModule_subsingleton_of_completelyFlat_powerTorsion a
      (baseChangeScalarModule φ) hS k N hN i hi)

/-- The actual base-changed tensor is computed by completing the left coefficient
and ordinarily extending the right power-torsion module. No Tor hypothesis on X is needed. -/
def powerTorsionCompletedBaseChangeTensorIso
    (hS : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (N : ModuleCat.{u} R)
    (k : ℕ) (hN : ∀ x : N, a ^ k • x = 0) :
    (boundedAboveDerivedBaseChange φ).obj
        (X ⊗ boundedAboveDerivedSingleFunctor.obj N) ≅
      (boundedAboveDerivedCompletionFunctor S (φ a)).obj
          ((boundedAboveDerivedBaseChange φ).obj X) ⊗
        boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj N) := by
  have hNS : ∀ x : (ModuleCat.extendScalars φ).obj N, (φ a) ^ k • x = 0 := by
    simpa only [map_pow] using scalarExtension_annihilated φ (a ^ k) N hN
  have := completionUnit_tensor_module_powerTorsion_isIso S (φ a)
    ((boundedAboveDerivedBaseChange φ).obj X) ((ModuleCat.extendScalars φ).obj N) k hNS
  exact boundedAboveDerivedTensorBaseChangeIso φ X (boundedAboveDerivedSingleFunctor.obj N) ≪≫
    boundedAboveDerivedTensor.mapIso
      (Iso.prod (Iso.refl _) (boundedAboveDerivedBaseChangeModuleAugmentationIso φ N
        (scalarExtensionTorVanishing_of_completelyFlat_powerTorsion φ a hS N k hN))) ≪≫
    asIso ((boundedAboveDerivedCompletionUnit S (φ a)).app
      ((boundedAboveDerivedBaseChange φ).obj X) ▷
        boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj N))

/-- This comparison preserves and reflects every target-base scalar annihilator in every degree. -/
lemma powerTorsionCompletedBaseChangeTensor_annihilated_iff
    (hS : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (N : ModuleCat.{u} R)
    (k : ℕ) (hN : ∀ x : N, a ^ k • x = 0) (i : ℤ) (s : S) :
    (∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (X ⊗ boundedAboveDerivedSingleFunctor.obj N)).obj, s • x = 0) ↔
    (∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
          ((boundedAboveDerivedBaseChange φ).obj X) ⊗
        boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj N)).obj,
      s • x = 0) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (powerTorsionCompletedBaseChangeTensorIso φ a hS X N k hN))
  constructor
  · intro h z
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective z
    rw [← e.toLinearEquiv.map_smul, h x, e.toLinearEquiv.map_zero]
  · intro h x
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.map_smul, h (e.toLinearEquiv x), e.toLinearEquiv.map_zero]

/-- Detect the original C-coefficient Tor scalar using the completed base-changed
coefficient and the ordinary extended test module, without assuming C is flat. -/
lemma torCoefficientScalar_eq_zero_iff_completed_baseChange_tensor_annihilated
    {C : Type u} [CommRing C] [Algebra R C]
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, a ^ k • x = 0) (i : ℕ) (s : R) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) (-(i : ℤ))).obj
        ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
            ((boundedAboveDerivedBaseChange φ).obj
              (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C))) ⊗
          boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj N)).obj,
        φ s • x = 0 :=
  (torCoefficientScalar_eq_zero_iff_powerTorsion_baseChange φ a hS N k hN i s).trans
    (powerTorsionCompletedBaseChangeTensor_annihilated_iff φ a hS.1
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)) N k hN (-(i : ℤ)) (φ s))

end SerrePositivity
