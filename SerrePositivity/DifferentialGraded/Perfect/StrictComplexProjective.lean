module
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexEnhancement
public import SerrePositivity.DifferentialGraded.Module.RingProjective
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # 既存の有限射影複体から一対象A上の主射影的dg加群へ -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 有界な各次数の射影性から既存のK-projective判定を使う。 -/
lemma strictlyPerfectComplex_isKProjective (P : Complex A)
    (hP : strictlyPerfectComplex A P) : P.IsKProjective := by
  obtain ⟨a, b, ha, hb⟩ := hP.1
  let := hb
  let (n : ℤ) : Module.Projective A (P.X n) := (hP.2 n).2
  exact CochainComplex.isKProjective_of_projective P b

/-- 有限射影複体を一対象Aのdg加群へ移すと、全Hom endの意味で射影的である。 -/
lemma strictlyPerfectComplex_ringModule_homotopicallyProjective (P : Complex A)
    (hP : strictlyPerfectComplex A P) :
    moduleHomotopicallyProjective A PUnit.{1}
      (ForgetEnrichment.of (Complex A) (ringModule A P)) :=
  (ringModule_homotopicallyProjective_iff A (ringModule A P)).2
    (strictlyPerfectComplex_isKProjective A P hP)

end SerrePositivity.DifferentialGraded
