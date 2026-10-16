module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelTensorModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelReconstruction
public import SerrePositivity.HomologicalAlgebra.ModelTensorHomologySurjective

/-! # Standard power quotient transitions and surjectivity of actual H0 transitions -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)

lemma powerPrincipalIdeal_antitone_step (n : ℕ) :
    Ideal.span {a ^ (n + 1)} ≤ Ideal.span {a ^ n} :=
  (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr ⟨a, pow_succ a n⟩)

def powerQuotientCoefficientTransition (n : ℕ) :
    ModuleCat.of R (R ⧸ Ideal.span {a ^ (n + 1)}) ⟶ ModuleCat.of R (R ⧸ Ideal.span {a ^ n}) :=
  ModuleCat.ofHom (Ideal.Quotient.factorₐ R (powerPrincipalIdeal_antitone_step a n)).toLinearMap

@[reassoc] lemma powerQuotientCoefficientMap_transition (n : ℕ) :
    powerQuotientCoefficientMap a (n + 1) ≫ powerQuotientCoefficientTransition a n =
      powerQuotientCoefficientMap a n := rfl

instance powerQuotientCoefficientTransition_epi (n : ℕ) :
    Epi (powerQuotientCoefficientTransition a n) :=
  epi_of_epi_fac (powerQuotientCoefficientMap_transition a n)

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The original cokernel transitions agree with the original quotient module maps. -/
@[reassoc] lemma powerCokernelTensorModelIso_transition
    (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    powerCokernelComplexTransition a K n ≫ (powerCokernelTensorModelIso a K hK n).hom =
      (powerCokernelTensorModelIso a K hK (n + 1)).hom ≫
        (moduleTensorCochainFunctor K).map (powerQuotientCoefficientTransition a n) := by
  apply (cancel_epi (cokernel.π (smulId (a ^ (n + 1)) K))).mp
  rw [← Category.assoc, powerCokernelComplexTransition_π, powerCokernelTensorModelIso_π]
  rw [← Category.assoc, powerCokernelTensorModelIso_π]
  simp only [powerQuotientTensorMap, Category.assoc, ← Functor.map_comp,
    powerQuotientCoefficientMap_transition]

/-- The H0 transitions of the actual cokernel tower are surjective under the
original pure flat mod-a input, including the zero-power stage. -/
lemma powerCokernel_homology_zero_transition_surjective
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hPure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj))
    (hFlat : Module.Flat (R ⧸ Ideal.span {a})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj)) (n : ℕ) :
    Function.Surjective (homologyMap
      (powerCokernelComplexTransition a (boundedAboveDerivedChosenModel X).complex n) 0) := by
  let P := (boundedAboveDerivedChosenModel X).complex
  have hP : ∀ i, Module.Flat R (P.X i) := by
    intro i
    have : Module.Projective R (P.X i) := inferInstance
    infer_instance
  have hs := modelTensor_homology_zero_map_surjective_of_power_annihilated a X hPure hFlat
    (n + 1) (powerQuotientCoefficientTransition a n) (fun x ↦ by
      change Ideal.Quotient.mk (Ideal.span {a ^ (n + 1)}) (a ^ (n + 1)) * x = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _), zero_mul])
  let H := homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
  have he : Epi (H.map ((moduleTensorCochainFunctor P).map
      (powerQuotientCoefficientTransition a n))) := (ModuleCat.epi_iff_surjective _).mpr hs
  have hw := congrArg H.map (powerCokernelTensorModelIso_transition a P hP n)
  simp only [Functor.map_comp] at hw
  have ht : Epi (H.map (powerCokernelComplexTransition a P n) ≫
      H.map (powerCokernelTensorModelIso a P hP n).hom) := by
    rw [hw]
    infer_instance
  have := (epi_comp_iff_of_isIso (H.map (powerCokernelComplexTransition a P n))
    (H.map (powerCokernelTensorModelIso a P hP n).hom)).mp ht
  exact (ModuleCat.epi_iff_surjective _).mp this

end SerrePositivity.DerivedCompletion
