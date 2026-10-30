module
public import SerrePositivity.DifferentialGraded.Verdier.U17
public import SerrePositivity.DifferentialGraded.Verdier.ChecksOrderSquare
public import SerrePositivity.DifferentialGraded.Checks.Verdier.ChecksScalarDirectCompletion
public import SerrePositivity.DifferentialGraded.Checks.Verdier.ChecksGraphPairMorita
public import SerrePositivity.DifferentialGraded.Checks.Verdier.ChecksKernelComparisonNaturality
public import SerrePositivity.DifferentialGraded.Checks.Verdier.ChecksKernelCompositionDescent
public import SerrePositivity.DifferentialGraded.Checks.Verdier.ChecksKernelCompositionNaturality

/-! # U17 の公開図式と公理監査の同時 import 検証 -/
@[expose] public section
set_option synthInstance.maxSize 1024
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
open SerrePositivity.Asymptotic

section Local
universe u v
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (h : localKFlat A D S)

example : (localPerfectKaroubiFirstEquivalence A D S h).functor.Linear A := inferInstance
example : (localPerfectKaroubiFirstEquivalence A D S h).CommShift ℤ := inferInstance
example : (localPerfectKaroubiFirstEquivalence A D S h).IsTriangulated := inferInstance
example : NatTrans.CommShift (localPerfectPaperSequenceComparison A D S h).hom ℤ := inferInstance
end Local

section Paper
variable (R : Type*) [CommRing R] [Nontrivial R] (s : ℕ → ℕ)
example : (paperRankEquivalence R s).functor.Linear R := inferInstance
example : (paperRankEquivalence R s).CommShift ℤ := inferInstance
example : (paperRankEquivalence R s).IsTriangulated := inferInstance
example : NatTrans.CommShift (paperSequenceComparison R s).hom ℤ := inferInstance
end Paper
