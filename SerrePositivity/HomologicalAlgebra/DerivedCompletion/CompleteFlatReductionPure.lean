module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPowerCokernelModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTower

/-! # Purity from a complete flat principal reduction over a bounded-torsion ring -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
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

lemma powerCokernel_homology_isZero_of_flat_reduction (n : ℕ) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology i) := by
  obtain ⟨hGE, hLE, _⟩ := derived_power_reduction_pure_flat a X hPure hFlat n
  apply powerCokernel_homology_isZero_of_reduction a n X i
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- All homology differences are surjective, using the actual H0 quotient transitions. -/
lemma powerCokernelHomologyDifference_surjective (i : ℤ) :
    Function.Surjective (complexTowerHomologyDifference R
      (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex)
      (powerCokernelComplexTransition a (boundedAboveDerivedChosenModel X).complex) i) := by
  apply moduleTowerDifference_surjective
  intro n
  by_cases hi : i = 0
  · subst i
    exact powerCokernel_homology_zero_transition_surjective a X hPure hFlat n
  · intro y
    have hz := powerCokernel_homology_isZero_of_flat_reduction a X hPure hFlat n i hi
    exact ⟨0, (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _⟩

lemma powerCokernel_holim_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((complexTowerHomotopyLimit R
      (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex)
      (powerCokernelComplexTransition a
        (boundedAboveDerivedChosenModel X).complex)).homology i) := by
  have hinj := complexTowerMilnorProjection_injective_of_surjective R _ _ i
    (powerCokernelHomologyDifference_surjective a X hPure hFlat (i - 1))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ hinj ?_⟩
  apply Subtype.ext
  funext n
  exact (ModuleCat.isZero_iff_subsingleton.mp
    (powerCokernel_homology_isZero_of_flat_reduction a X hPure hFlat n i hi)).elim _ _

/-- The actual H0 is the inverse limit of the ordinary power-reduction H0 modules. -/
def completeFlatReductionH0LimitIso
    (hR : ∃ N : ℕ, ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a X.obj) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj ≅
      ModuleCat.of R (moduleTowerLimit R
        (fun n ↦ (powerCokernelComplex a (boundedAboveDerivedChosenModel X).complex n).homology 0)
        (fun n ↦ (homologyMap
          (powerCokernelComplexTransition a
            (boundedAboveDerivedChosenModel X).complex n) 0).hom)) := by
  let P := boundedAboveDerivedChosenModel X
  have hP : ∀ i, Module.Flat R (P.complex.X i) := by
    intro i
    have : Module.Projective R (P.complex.X i) := inferInstance
    infer_instance
  let N := Classical.choose hR
  have hN := Classical.choose_spec hR
  have hcP := isComplete_of_iso R a P.iso.symm hc
  have := powerCokernelReconstruction_quasiIso a P.complex hP N hN hcP
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso P.iso.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).app P.complex ≪≫
    asIso (homologyMap (powerCokernelReconstruction a P.complex) 0) ≪≫
    (complexTowerMilnorProjectionEquiv R _ _ 0
      (powerCokernelHomologyDifference_surjective a X hPure hFlat (-1))).toModuleIso

/-- G9 purity: no regularity, finite generation, Noetherianity, or classical completeness. -/
theorem derived_pure_of_complete_flat_reduction
    (hR : ∃ N : ℕ, ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a X.obj) : X.obj.IsGE 0 ∧ X.obj.IsLE 0 := by
  let P := boundedAboveDerivedChosenModel X
  have hP : ∀ i, Module.Flat R (P.complex.X i) := by
    intro i
    have : Module.Projective R (P.complex.X i) := inferInstance
    infer_instance
  obtain ⟨N, hN⟩ := hR
  have hcP := isComplete_of_iso R a P.iso.symm hc
  have := powerCokernelReconstruction_quasiIso a P.complex hP N hN hcP
  have hX (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X.obj) := by
    have hz := powerCokernel_holim_homology_isZero a X hPure hFlat i hi
    have hpz := hz.of_iso (asIso (homologyMap (powerCokernelReconstruction a P.complex) i))
    exact hpz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso P.iso.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P.complex)
  exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i hi ↦ hX i (by omega)),
    (DerivedCategory.isLE_iff _ _).mpr (fun i hi ↦ hX i (by omega))⟩

end SerrePositivity.DerivedCompletion
