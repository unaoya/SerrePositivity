module
public import SerrePositivity.DifferentialGraded.Perfect.Ring.FiniteProjectiveComparison
public import Mathlib.Data.ZMod.Basic

/-! # 一対象Aのperfect比較とretractの受入監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Idempotents
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example : (ringPerfectKaroubiRealization A).IsEquivalence := inferInstance
example : (ringPerfectKaroubiRealization A).Full := inferInstance
example : (ringPerfectKaroubiRealization A).Faithful := inferInstance
example : (ringPerfectKaroubiRealization A).Linear A := inferInstance
example : (ringPerfectKaroubiEquivalence A).inverse.Linear A := inferInstance
example : (ringPerfectKaroubiEquivalence A).inverse.Additive := inferInstance
example : (ringPerfectKaroubiEquivalence A).CommShift ℤ := inferInstance
example : (ringPerfectKaroubiEquivalence A).IsTriangulated := inferInstance
example : toKaroubi (SerrePositivity.PerfectHomotopy A) ⋙ ringPerfectKaroubiRealization A ≅
    perfectHomotopyToDGPerfect A := ringPerfectKaroubiRealization_fac A
example : (ringPerfectKaroubiEquivalence (ZMod 2)).IsTriangulated := inferInstance

#print axioms ringPerfectKaroubiFunctor
#print axioms ringPerfectKaroubiFunctorFull
#print axioms ringPerfectKaroubiFunctorFaithful
#print axioms ringPerfectKaroubiFunctorEssSurj
#print axioms ringPerfectKaroubiFunctorIsEquivalence
#print axioms ringPerfectKaroubiFunctorAdditive
#print axioms ringPerfectKaroubiFunctorLinear
#print axioms ringPerfectKaroubiFunctorCommShift
#print axioms ringPerfectKaroubiFunctorIsTriangulated
#print axioms ringPerfectKaroubiRealization
#print axioms ringPerfectKaroubiRealizationIsEquivalence
#print axioms ringPerfectKaroubiRealizationAdditive
#print axioms ringPerfectKaroubiRealizationLinear
#print axioms ringPerfectKaroubiRealizationToKaroubiIso
#print axioms ringPerfectKaroubiRealizationCommShift
#print axioms ringPerfectKaroubiRealizationToKaroubiIsoCommShift
#print axioms ringPerfectKaroubiRealizationIsTriangulated
#print axioms ringPerfectKaroubiRealization_fac
#print axioms ringPerfectKaroubiEquivalence
#print axioms ringPerfectKaroubiEquivalenceFunctorLinear
#print axioms ringPerfectKaroubiEquivalenceFunctorAdditive
#print axioms ringPerfectKaroubiEquivalenceFunctorCommShift
#print axioms ringPerfectKaroubiEquivalenceInverseCommShift
#print axioms ringPerfectKaroubiEquivalenceCommShift
#print axioms ringPerfectKaroubiEquivalenceIsTriangulated
