module
public import SerrePositivity.HomologicalAlgebra.DerivedKoszulDescent
public import SerrePositivity.HomologicalAlgebra.CompleteTwoCohomologyAnnihilator

/-! # Conditional scalar isogeny descent for complete two-cohomology objects -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- Compare actual Koszul homology with the standard representative tower used by Milnor. -/
def derivedKoszulStageHomologyEquiv (a : R) (X : DerivedCategory (ModuleCat.{u} R))
    (n : ℕ) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((derivedScalarConeFunctor R (a ^ n)).obj X) ≃ₗ[R]
      (complexPowerKoszulStage R a (DerivedCategory.Q.objPreimage X) n).homology i :=
  ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      ((derivedScalarConeFunctor R (a ^ n)).mapIso
          (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
        (derivedScalarConeComparison R (a ^ n)).app (DerivedCategory.Q.objPreimage X)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app
      ((scalarConeFunctor (a ^ n)).obj (DerivedCategory.Q.objPreimage X))).toLinearEquiv

/-- Actual Koszul-stage annihilation passes through the standard complete Milnor comparison. -/
lemma completeDerived_homology_pow_annihilated_of_derivedKoszul (a : R)
    (X : DerivedCategory (ModuleCat.{u} R)) (hX : IsComplete R a X)
    (i : ℤ) (g : R) (N : ℕ)
    (h : ∀ n : ℕ,
      (∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((derivedScalarConeFunctor R (a ^ n)).obj X), g ^ N • x = 0) ∧
      (∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) (i - 1)).obj
        ((derivedScalarConeFunctor R (a ^ n)).obj X), g ^ N • x = 0)) :
    ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X, g ^ (2 * N) • x = 0 := by
  apply completeDerived_homology_pow_annihilated R a X hX i g N
  intro n
  constructor
  · intro x
    let e := derivedKoszulStageHomologyEquiv R a X n i
    have hx := congrArg e ((h n).1 (e.symm x))
    simpa only [map_smul, map_zero, LinearEquiv.apply_symm_apply] using hx
  · intro x
    let e := derivedKoszulStageHomologyEquiv R a X n (i - 1)
    have hx := congrArg e ((h n).2 (e.symm x))
    simpa only [map_smul, map_zero, LinearEquiv.apply_symm_apply] using hx

/-- Scalar-cone reduction is linear on the actual derived category. -/
instance derivedScalarConeFunctor_linear (a : R) :
    (derivedScalarConeFunctor R a).Linear R := by
  let : Localization.Lifting
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (scalarConeFunctor a ⋙ DerivedCategory.Q) (derivedScalarConeFunctor R a) :=
    ⟨derivedScalarConeComparison R a⟩
  exact (Localization.functor_linear_iff
    (DerivedCategory.Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) R
    (scalarConeFunctor a ⋙ DerivedCategory.Q) (derivedScalarConeFunctor R a)).mp inferInstance

/-- A derived scalar zero map gives the same annihilator on all scalar-cone homology. -/
lemma derivedScalarCone_homology_annihilated_of_scalar_eq_zero (a : R)
    (X : DerivedCategory (ModuleCat.{u} R)) (r : R) (hX : r • 𝟙 X = 0) (i : ℤ) :
    ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X), r • x = 0 := by
  have hz : (derivedScalarConeFunctor R a).map (0 : X ⟶ X) = 0 := by
    simpa only [zero_smul] using (derivedScalarConeFunctor R a).map_smul (0 : R) (𝟙 X)
  have h := congrArg ((derivedScalarConeFunctor R a).map) hX
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, hz] at h
  have hH := congrArg ((DerivedCategory.homologyFunctor (ModuleCat R) i).map) h
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at hH
  intro x
  exact congrArg (fun f => f.hom x) hH

variable {R} {S : Type u} [CommRing S] (φ : R →+* S)

/-- A uniform power-Koszul annihilator after completely faithful flat extension descends. -/
lemma complete_two_cohomology_scalar_pow_eq_zero_of_completelyFaithfullyFlat
    (a : R) (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (hX : IsComplete R a X.obj)
    (lo hi : ℤ) (hlohi : lo + 1 = hi) [X.obj.IsGE lo] [X.obj.IsLE hi] (g : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ i ∈ ({lo, lo - 1, hi, hi - 1} : Set ℤ),
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj X)).obj, (φ g) ^ N • x = 0) :
    g ^ (4 * N) • 𝟙 X.obj = 0 := by
  have hR : ∀ n : ℕ, ∀ i ∈ ({lo, lo - 1, hi, hi - 1} : Set ℤ),
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((derivedScalarConeFunctor R (a ^ n)).obj X.obj), g ^ N • x = 0 := by
    intro n i hi
    apply (derivedKoszulHomology_annihilated_iff φ a hS n X (g ^ N) i).mp
    simpa only [map_pow] using h n i hi
  have hLo := completeDerived_homology_pow_annihilated_of_derivedKoszul R a X.obj hX lo g N
    (fun n => ⟨hR n lo (by simp), hR n (lo - 1) (by simp)⟩)
  have hHi := completeDerived_homology_pow_annihilated_of_derivedKoszul R a X.obj hX hi g N
    (fun n => ⟨hR n hi (by simp), hR n (hi - 1) (by simp)⟩)
  have hz := two_cohomology_scalar_pow_eq_zero R X.obj lo hi hlohi g (2 * N) hLo hHi
  simpa only [← Nat.mul_assoc] using hz

end SerrePositivity
