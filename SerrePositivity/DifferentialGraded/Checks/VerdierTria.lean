module
public import SerrePositivity.DifferentialGraded.Verdier.NullObjects

/-! # tria の生成性・Verdier 核・後続比較の型と公理監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (P : ObjectProperty (TriaCategory A D)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] :
    triaImage A D S ≤ P ↔ ∀ x ∈ S, P (triaRepresentable A D x) :=
  triaImage_le_iff_generators A D S P

example (S : Set D) (X : TriaCategory A D) :
    IsZero ((triaQuotient A D S).obj X) ↔ modulePerfectOver A D S X.obj :=
  triaQuotient_isZero_iff_perfect A D S X

example (X : TriaCategory A D) :
    IsZero ((triaQuotient A D ∅).obj X) ↔ triaNull A D ∅ X :=
  triaQuotient_isZero_iff_triaNull A D ∅ X

example (S : Set D) :
    triaKaroubiFirst A D S ⋙ (triaKaroubiOrderEquivalence A D S).functor ≅
      triaQuotient A D S ⋙ CategoryTheory.Idempotents.toKaroubi _ :=
  triaKaroubiComparison A D S

#print axioms triaImage_le_iff_generators
#print axioms verdierQuotient_isZero_iff_retractClosure
#print axioms verdierQuotient_kernel_eq_retractClosure
#print axioms triangEnvelope_eq_retractClosure
#print axioms triaImage_retractClosure_iff_perfect
#print axioms triaQuotient_isZero_iff
#print axioms triaQuotient_isZero_iff_triaNull
#print axioms triaQuotient_isZero_iff_perfect
#print axioms triaKaroubiOrderEquivalence
#print axioms triaKaroubiComparison
