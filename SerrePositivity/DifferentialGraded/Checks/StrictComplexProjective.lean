module
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexProjective
public import Mathlib.Data.ZMod.Basic

/-! # 一対象Aの全Hom射影性と有限射影複体の比較の監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example (P N : Complex A) [P.IsKProjective] (hN : N.Acyclic) :
    (homComplex A P N).Acyclic := homComplex_acyclic_of_isKProjective A P N hN
example (P : Complex A) : P.IsKProjective ↔
    ∀ N : Complex A, N.Acyclic → (homComplex A P N).Acyclic :=
  isKProjective_iff_homComplex_acyclic A P
example (M : RightModule A PUnit.{1}) :
    moduleHomotopicallyProjective A PUnit.{1} (ForgetEnrichment.of (Complex A) M) ↔
      (M.obj (op PUnit.unit)).IsKProjective := ringModule_homotopicallyProjective_iff A M
example (P : StrictPerfectDGComplex A) : P.val.IsKProjective :=
  strictlyPerfectComplex_isKProjective A P.val P.property
example (P : StrictPerfectDGComplex A) :
    moduleHomotopicallyProjective A PUnit.{1}
      (ForgetEnrichment.of (Complex A) ((ringConstantDG A).obj P.val)) :=
  strictlyPerfectComplex_ringModule_homotopicallyProjective A P.val P.property
example (P : StrictPerfectDGComplex (ZMod 2)) :
    moduleHomotopicallyProjective (ZMod 2) PUnit.{1}
      (ForgetEnrichment.of (Complex (ZMod 2)) (ringModule (ZMod 2) P.val)) :=
  strictlyPerfectComplex_ringModule_homotopicallyProjective (ZMod 2) P.val P.property

#print axioms homComplex_acyclic_of_isKProjective
#print axioms isKProjective_of_homComplex_acyclic
#print axioms isKProjective_iff_homComplex_acyclic
#print axioms ringModule_homotopicallyProjective_iff
#print axioms strictlyPerfectComplex_isKProjective
#print axioms strictlyPerfectComplex_ringModule_homotopicallyProjective
