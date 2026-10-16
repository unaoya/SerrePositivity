import SerrePositivity.BhattScholze.PerfectDeltaCartierTensorComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientIso
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotient_pure
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierIso
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedResidueTensor_pure
assert_no_sorry SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierH0Iso

#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientIso
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotient_pure
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierIso
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedResidueTensor_pure
#print axioms SerrePositivity.BhattScholze.perfectDelta_completedResidueTensorCartierH0Iso

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra principalAdicQuotientAlgebra

-- Actual perfect prisms supply all three completeness inputs; no residue flatness is supplied.
example (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (PR : OrientedPrism p R) (PS : OrientedPrism p S) (PT : OrientedPrism p T)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (hT : PT.deltaStructure.IsPerfect) (fS : OrientedPrism.Hom PR PS) (fT : OrientedPrism.Hom PR PT)
    (hfS : fS.toRingHom = algebraMap R S) (hfT : fT.toRingHom = algebraMap R T) :
    let Q := R ⧸ Ideal.span {PR.generator}
    let SQ := S ⧸ Ideal.map (algebraMap R S) (Ideal.span {PR.generator})
    let TQ := T ⧸ Ideal.map (algebraMap R T) (Ideal.span {PR.generator})
    let RES := boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ
    RES.X.obj.IsGE 0 ∧ RES.X.obj.IsLE 0 := by
  letI := PR.isAdicComplete_p_of_perfect hR
  letI := PS.isAdicComplete_p_of_perfect hS
  letI := PT.isAdicComplete_p_of_perfect hT
  have hRS : PR.deltaStructure.IsDeltaHom PS.deltaStructure (algebraMap R S) := by
    simpa only [hfS] using fS.map_delta
  have hRT : PR.deltaStructure.IsDeltaHom PT.deltaStructure (algebraMap R T) := by
    simpa only [hfT] using fT.map_delta
  exact perfectDelta_completedResidueTensor_pure p R S T PR.deltaStructure PS.deltaStructure
    PT.deltaStructure hR hS hT hRS hRT PR.generator (PR.isDistinguished_of_perfect hR)

-- The usual Cartier quotient, not a chosen abstract isomorphic module, is the target.
example (R : Type u) [CommRing R] (d : R) (hd : IsSMulRegular R d)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0]
    (hreg : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) d) :
    let H := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {d})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj A.X).obj ≅
      ModuleCat.of (R ⧸ Ideal.span {d}) (H ⧸ Ideal.span {algebraMap R H d}) :=
  pureDerivedAlgebraCartierQuotientH0Iso R d hd A hreg

-- A unit Cartier generator gives a zero quotient ring and is included in the common comparison.
example (R : Type u) [CommRing R]
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0] :
    ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(1 : R)}))).obj A.X).obj.IsGE 0 ∧
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(1 : R)}))).obj A.X).obj.IsLE 0 :=
  pureDerivedAlgebraCartierQuotient_pure R 1
    (by intro x y h; simpa only [one_smul] using h) A
    (by intro x y h; simpa only [one_smul] using h)
