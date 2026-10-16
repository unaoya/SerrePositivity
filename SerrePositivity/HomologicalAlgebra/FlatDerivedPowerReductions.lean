module

public import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction
public import SerrePositivity.HomologicalAlgebra.ScalarExtensionTensorTests

/-! # A pure flat principal reduction gives pure flat reductions at every power -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
include hPure hFlat

/-- The G10 coefficient filtration also works on modules annihilated by a power
without requiring nilpotence of a on the original coefficient ring. -/
lemma modelTensor_isZero_of_power_annihilated (n : ℕ) (N : ModuleCat.{u} R)
    (hN : ∀ x : N, a ^ n • x = 0) (i : ℤ) (hi : i ≠ 0) :
    IsZero (((moduleTensorCochainFunctor
      (boundedAboveDerivedChosenModel X).complex).obj N).homology i) := by
  let P := (boundedAboveDerivedChosenModel X).complex
  have hP : ∀ j, Module.Flat R (P.X j) := by
    intro j
    have : Module.Projective R (P.X j) := inferInstance
    infer_instance
  apply moduleProperty_of_idealPower_annihilated (Ideal.span {a})
    (fun N ↦ IsZero (((moduleTensorCochainFunctor P).obj N).homology i))
    (fun N hN ↦ modelTensor_homology_isZero_of_flat_reduction
      (Ideal.span {a}) X hPure hFlat N hN i hi)
    (moduleTensorCochain_homology_isZero_extension P hP i) n N
  intro r hr x
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [mul_smul, smul_comm, hN x, smul_zero]

/-- All actual power reductions are pure with flat H0, including power zero.
There are no completeness, regularity, or Noetherian hypotheses. -/
theorem derived_power_reduction_pure_flat (n : ℕ) :
    ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj.IsGE 0 ∧
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj.IsLE 0 ∧
      Module.Flat (R ⧸ Ideal.span {a ^ n})
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a ^ n})) 0).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj X).obj) := by
  apply derivedBaseChange_pure_flat_of_tensor_tests (Ideal.Quotient.mk (Ideal.span {a ^ n})) X
  intro N i hi
  apply modelTensor_isZero_of_power_annihilated a X hPure hFlat n _ ?_ i hi
  intro x
  change (Ideal.Quotient.mk (Ideal.span {a ^ n}) (a ^ n)) • x = 0
  rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _), zero_smul]

end SerrePositivity
