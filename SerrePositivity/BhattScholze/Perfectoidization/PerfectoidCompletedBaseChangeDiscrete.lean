module
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidCompletedTensorDiscrete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.RingEquivDerivedTensor
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.PowerTorsionCompletedBaseChange

/-! # The actual completed scalar extension of perfectoid coefficients is discrete

The target scalar ring is retained throughout restriction, completion, and the
normalized comparison with the actual zeroth homology module.
-/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory MonoidalCategory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R S C : Type u)
    [CommRing R] [CommRing S] [CommRing C] [Algebra R S] [Algebra R C]

/-- Complete the original actual scalar extension over S; its discreteness
follows from the original perfectoid tensor over R after restriction. -/
lemma integralPerfectoid_completedBaseChange_pure
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hC : IsIntegralPerfectoid C p) :
    let X := (boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 := by
  let φ := algebraMap R S
  let M := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)
  let X := (boundedAboveDerivedBaseChange φ).obj M
  let eS : derivedBaseChangeScalarObject φ ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S) :=
    boundedAboveDerivedSingleFunctor.mapIso (algebraSelfRestrictionIso R S)
  let B := boundedAboveCompletedTensorAlgebra R (p : R) S C
  let Y := (boundedAboveDerivedCompletionFunctor S (p : S)).obj X
  let e0 := ((boundedAboveCompletionRestrictionIso φ (p : R)).app X).symm ≪≫
    (boundedAboveDerivedCompletionFunctor R (p : R)).mapIso
      (boundedAboveDerivedBaseChangeTensorIso φ M ≪≫
        boundedAboveDerivedTensor.mapIso (Iso.prod eS (Iso.refl M)))
  have hpure := integralPerfectoid_completedTensor_pure p R S C hR hS hC
  letI : B.X.obj.IsGE 0 := hpure.1
  letI : B.X.obj.IsLE 0 := hpure.2
  let e : (derivedRestrictScalars φ).obj Y.obj ≅ B.X.obj := by
    have he := DerivedCategory.Minus.ι.mapIso e0
    change (derivedRestrictScalars φ).obj
        ((derivedComplexCompletionFunctor S (φ (p : R))).obj X.obj) ≅
      (derivedComplexCompletionFunctor R (p : R)).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S), M)).obj at he
    change (derivedRestrictScalars φ).obj
        ((derivedComplexCompletionFunctor S (p : S)).obj X.obj) ≅
      (derivedComplexCompletionFunctor R (p : R)).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S), M)).obj
    rw [map_natCast] at he
    exact he
  have hlo := DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  have hhi := DerivedCategory.TStructure.t.isLE_of_iso e.symm 0
  exact ⟨(derivedRestrictScalars_isGE_iff φ Y.obj 0).mp hlo,
    (derivedRestrictScalars_isLE_iff φ Y.obj 0).mp hhi⟩

/-- The S-linear comparison is normalized by the identity on the actual H⁰ module. -/
def integralPerfectoid_completedBaseChangeSingleIso
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hC : IsIntegralPerfectoid C p) :
    let X := (boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))
    X ≅ boundedAboveDerivedSingleFunctor.obj
      ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj X.obj) := by
  dsimp only
  have h := integralPerfectoid_completedBaseChange_pure p R S C hR hS hC
  letI := h.1
  letI := h.2
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso _ 0)

/-- Original Tor coefficient actions are detected by ordinary Tor over the new base,
using the actual H⁰ of the completed coefficient extension. -/
lemma integralPerfectoid_torCoefficientScalar_eq_zero_iff_completedBaseChangeTor
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hC : IsIntegralPerfectoid C p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R S)))
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (i : ℕ) (s : R) :
    let X := (boundedAboveDerivedCompletionFunctor S (p : S)).obj
      ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))
    let M := (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj X.obj
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
      ∀ x : (((Tor (ModuleCat S) i).obj M).obj ((ModuleCat.extendScalars
        (algebraMap R S)).obj N)), algebraMap R S s • x = 0 := by
  let X := (boundedAboveDerivedCompletionFunctor S (p : S)).obj
    ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))
  let M := (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj X.obj
  let L := (ModuleCat.extendScalars (algebraMap R S)).obj N
  have ht : torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) (-(i : ℤ))).obj
        (X ⊗ boundedAboveDerivedSingleFunctor.obj L).obj, algebraMap R S s • x = 0 := by
    have h := torCoefficientScalar_eq_zero_iff_completed_baseChange_tensor_annihilated
      (C := C) (algebraMap R S) (p : R) hflat N k hN i s
    rw [map_natCast] at h
    exact h
  let eX := integralPerfectoid_completedBaseChangeSingleIso p R S C hR hS hC
  let e := (DerivedCategory.homologyFunctor (ModuleCat S) (-(i : ℤ))).mapIso
      (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensor.mapIso
        (Iso.prod eX (Iso.refl (boundedAboveDerivedSingleFunctor.obj L))))) ≪≫
    (boundedAboveDerivedTensorModuleTorNatIso M i).app L
  apply ht.trans
  constructor
  · intro h z
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective z
    rw [← e.toLinearEquiv.map_smul, h x, e.toLinearEquiv.map_zero]
  · intro h x
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.map_smul, h (e.toLinearEquiv x), e.toLinearEquiv.map_zero]

end SerrePositivity.BhattScholze
