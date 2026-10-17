module
public import SerrePositivity.DifferentialGraded.Verdier.U17
public import SerrePositivity.DifferentialGraded.Verdier.ChecksOrderSquare
public import SerrePositivity.DifferentialGraded.Verdier.ChecksComparisonLinear
public import SerrePositivity.DifferentialGraded.Verdier.ChecksSupportSquare
public import SerrePositivity.DifferentialGraded.Verdier.ChecksRetractSquare
public import SerrePositivity.DifferentialGraded.Verdier.ChecksGraphPerfectSquare
public import SerrePositivity.DifferentialGraded.Verdier.ChecksDerivedKernelGraphSquare
public import SerrePositivity.DifferentialGraded.Verdier.ChecksKernelLocalPerfectSquare
public import SerrePositivity.DifferentialGraded.Verdier.ChecksPerfectKernelVerdier
public import SerrePositivity.DifferentialGraded.Verdier.ChecksCompletionSquareShift
public import SerrePositivity.DifferentialGraded.Verdier.ChecksScalarKaroubiShift
public import SerrePositivity.DifferentialGraded.Verdier.ChecksScalarQuotientSourceSquare
public import SerrePositivity.DifferentialGraded.Verdier.ChecksScalarDirectCompletion
public import SerrePositivity.DifferentialGraded.Verdier.ChecksGraphPairMorita
public import SerrePositivity.DifferentialGraded.Verdier.ChecksKernelComparisonNaturality
public import SerrePositivity.DifferentialGraded.Verdier.ChecksKernelCompositionDescent

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
