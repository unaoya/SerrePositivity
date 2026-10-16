module
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionDerivedComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraRestriction
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
/-! # Principal completion of pure derived algebras with regular H⁰ scalar -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a)
include ha in
/-- Completing the coefficient ring at a regular scalar preserves degree-zero concentration. -/
lemma completedUnitAlgebra_pure_of_regular :
    (completedUnitAlgebra R a).X.obj.IsGE 0 ∧ (completedUnitAlgebra R a).X.obj.IsLE 0 := by
  let X0 := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)
  let X := (boundedAboveDerivedCompletionFunctor R a).obj X0
  have hc := derivedComplexCompletionFunctor_isComplete R a X0.obj
  have hpure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj) := by
    intro i hi
    let ec : (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X ≅
        (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X0 := by
      have e := (boundedAboveDerivedCompletionQuotientIso R a ha 1 X0).symm
      rw [pow_one] at e
      exact e
    let e := ec ≪≫ derivedQuotientModuleIsoOfRegular a ha (ModuleCat.of R R) ha
    exact (derivedSingleHomology_isZero _ i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).mapIso
        (DerivedCategory.Minus.ι.mapIso e))
  have h := derived_pure_of_complete_regular_quotient_pure a ha X hc hpure
  exact ⟨h.1, h.2.1⟩

/-- Regularity is required in the coefficient algebra, with no regularity assumption on the base. -/
lemma completedAlgebra_pure_of_regular (S : Type u) [CommRing S] [Algebra R S]
    (hs : IsSMulRegular S (algebraMap R S a)) :
    (completedAlgebra R a S).X.obj.IsGE 0 ∧ (completedAlgebra R a S).X.obj.IsLE 0 := by
  let Y := completedUnitAlgebra S (algebraMap R S a)
  have h := completedUnitAlgebra_pure_of_regular S (algebraMap R S a) hs
  let hge : Y.X.obj.IsGE 0 := h.1
  let hle : Y.X.obj.IsLE 0 := h.2
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj (completedAlgebra R a S).X.obj) := by
    have hy : IsZero ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj Y.X.obj) := by
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    let e := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
        (completedAlgebraRestrictionIso R a S) ≪≫
      (derivedRestrictScalarsHomologyIso (algebraMap R S) i).app Y.X.obj
    exact ((ModuleCat.restrictScalars (algebraMap R S)).map_isZero hy).of_iso e
  exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i hi => hz i (by omega)),
    (DerivedCategory.isLE_iff _ _).mpr (fun i hi => hz i (by omega))⟩


/-- A pure derived algebra stays pure after completion at a scalar regular on its actual H⁰. -/
lemma derivedAlgebra_completion_pure_of_h0_regular
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0] :
    let B := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    IsSMulRegular B (algebraMap R B a) →
      ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj.IsGE 0 ∧
      ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj.IsLE 0 := by
  dsimp only
  let B := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  intro hreg
  have hp := completedAlgebra_pure_of_regular R a B hreg
  let hge : (completedAlgebra R a B).X.obj.IsGE 0 := hp.1
  let hle : (completedAlgebra R a B).X.obj.IsLE 0 := hp.2
  let e := (derivedComplexCompletionFunctor R a).mapIso (normalizedPureHomologyIso A.X.obj 0)
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj) := by
    have hy : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        (completedAlgebra R a B).X.obj) := by
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    exact hy.of_iso ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e)
  exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i hi => hz i (by omega)),
    (DerivedCategory.isLE_iff _ _).mpr (fun i hi => hz i (by omega))⟩

end SerrePositivity.DerivedCompletion
