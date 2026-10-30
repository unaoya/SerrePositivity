module
public import SerrePositivity.DifferentialGraded.Verdier.ScalarDirectCompletion
public import Mathlib.Data.ZMod.Basic

/-! # 直接局所化した係数変更の完備化比較の監査と非平坦な係数変更の例 -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor Idempotents
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms sourceScalarCompletedFunctor
#print axioms sourceScalarCompletedFunctorIsTriangulated
#print axioms sourceScalarCompletedFactorsCommShift
#print axioms sourceScalarCompletedFactorsTriangle
#print axioms sourceScalarCompletedTransportIso
#print axioms sourceScalarCompletedTriaSquare
#print axioms sourceScalarCompletedPerfectSquare
#print axioms sourceScalarCompletedLocalPerfectSquare
#print axioms sourceScalarCompletionComparisonIso

/-- 整数から mod 2 への変更でも、直接局所化の標準 Karoubi 正方形に平坦性は不要。 -/
example (D : Type) [DGCategory ℤ D] [Small.{0} D] (S : Set D) :
    toKaroubi (TriaQuotient ℤ D S) ⋙
        sourceScalarCompletedFunctor (Int.castRingHom (ZMod 2)) D S ≅
      sourceScalarVerdierFunctor (Int.castRingHom (ZMod 2)) D S ⋙
        toKaroubi (TriaQuotient (ZMod 2)
          (ScalarExtension.DGBaseChange (Int.castRingHom (ZMod 2)) D) S) :=
  sourceScalarCompletedFactors (Int.castRingHom (ZMod 2)) D S
