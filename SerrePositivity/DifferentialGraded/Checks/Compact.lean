module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 非有界複体の有限supportと代表加群のcompact性 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (x : D) : moduleCompact A D ((moduleToDerived A D).obj
    (ForgetEnrichment.of (Complex A) (representable A x))) := moduleRepresentable_compact A D x

example {J : Type u} (x : D) (F : J → DerivedModuleCategory A D) :
    DirectSum J (fun j => (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ F j) ≃ₗ[A]
        ((moduleToDerived A D).obj
          (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ ∐ F) :=
  moduleCompactHomLinearEquiv A D (moduleRepresentable_compact A D x) F

example : (moduleCompact A D).IsStableUnderRetracts := inferInstance
example : (moduleCompact A D).IsClosedUnderIsomorphisms := inferInstance

example {J : Type u} (F : J → Complex A) (s : Cofan F) (hs : IsColimit s)
    (n : ℤ) (z : complexCycles A s.pt n) :
    ∃ (t : Finset J) (c : ∀ j, complexCycles A (F j) n),
      ∑ j ∈ t, (s.inj j).f n (c j).val = z.val := complexCofan_cycle_rep A F s hs n z

example (F : ℕ → DerivedModuleCategory (ZMod 2) PUnit.{1}) :
    Function.Bijective (moduleCompactComparison (ZMod 2) PUnit.{1}
      ((moduleToDerived (ZMod 2) PUnit.{1}).obj
        (ForgetEnrichment.of (Complex (ZMod 2)) (representable (ZMod 2) PUnit.unit))) F) :=
  (moduleCompact_iff_comparison_bijective (ZMod 2) PUnit.{1} _).mp
    (moduleRepresentable_compact (ZMod 2) PUnit.{1} PUnit.unit) ℕ F

#print axioms moduleCofan_element_rep
#print axioms complexCofan_element_rep
#print axioms complexCofan_cycle_rep
#print axioms complexZeroHomologyClassLinearMap
#print axioms complexZeroHomologyClass_surjective
#print axioms complexZeroHomologyClass_sum
#print axioms complexCofan_zeroHomology_rep
#print axioms moduleRepresentableDerivedCoproduct_rep
#print axioms moduleCompact
#print axioms moduleRepresentable_compact
#print axioms derivedPostcomposeLinearMap
#print axioms moduleCompactComparison
#print axioms moduleCompactComparison_lof
#print axioms moduleCompactComparison_injective
#print axioms moduleCompact_iff_comparison_surjective
#print axioms moduleCompact_iff_comparison_bijective
#print axioms moduleCompactHomLinearEquiv
#print axioms moduleCompact_of_retract
#print axioms moduleCompactStableUnderRetracts
#print axioms moduleCompactClosedUnderIso
#print axioms moduleCompact_of_isZero
