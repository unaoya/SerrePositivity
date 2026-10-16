module

public import SerrePositivity.HomologicalAlgebra.FlatDerivedPowerReductions
public import Mathlib.Algebra.Homology.HomologySequence

/-! # Surjectivity on H0 for power-annihilated coefficient quotients -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)

/-- Pure flat reduction makes H0 of the original model preserve surjections
between power-annihilated coefficients. -/
lemma modelTensor_homology_zero_map_surjective_of_power_annihilated
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (n : ℕ) {N N' : ModuleCat.{u} R} (f : N ⟶ N') [Epi f]
    (hN : ∀ x : N, a ^ n • x = 0) :
    Function.Surjective (homologyMap
      ((moduleTensorCochainFunctor (boundedAboveDerivedChosenModel X).complex).map f) 0) := by
  let P := (boundedAboveDerivedChosenModel X).complex
  let F := moduleTensorCochainFunctor P
  let S : ShortComplex (ModuleCat.{u} R) := ShortComplex.mk (kernel.ι f) f (kernel.condition _)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel _, mono_f := inferInstance, epi_g := inferInstance }
  have hP : ∀ i, Module.Flat R (P.X i) := by
    intro i
    have : Module.Projective R (P.X i) := inferInstance
    infer_instance
  have hk : ∀ x : (kernel f : ModuleCat.{u} R), a ^ n • x = 0 := by
    intro x
    apply (ModuleCat.mono_iff_injective (kernel.ι f)).mp inferInstance
    simpa only [map_smul, map_zero] using hN (kernel.ι f x)
  have hz := modelTensor_isZero_of_power_annihilated a X hPure hFlat n (kernel f) hk 1 (by omega)
  have he := (moduleTensorCochain_shortExact P hP S hS).homology_exact₃ 0 1 rfl
  have hep : Epi (homologyMap (F.map f) 0) := he.epi_f (hz.eq_of_tgt _ _)
  exact (ModuleCat.epi_iff_surjective _).mp hep

end SerrePositivity
