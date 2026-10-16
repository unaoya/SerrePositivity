module
public import SerrePositivity.DifferentialGraded.Perfect.RingFiniteCell
public import SerrePositivity.DifferentialGraded.Perfect.RingEnhancement

/-! # 一対象Aの有限cellは有限射影dg複体比較のH⁰本質像に入る -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A]

/-- 実際の有限cell代表を持つ主perfect dg対象は、有限射影複体の比較の像となる。 -/
lemma strictPerfectDGComplexToPerfectDG_essImage_of_finiteCell
    (X : HomotopyCategory A (PerfectDGModule A PUnit.{1}))
    (hX : moduleFiniteCell A PUnit.{1}
      (ForgetEnrichment.of (Complex A)
        (ForgetEnrichment.to (Complex A) X.as).val)) :
    (strictPerfectDGComplexToPerfectDG A).onHomotopy.essImage X := by
  let M : PerfectDGModule A PUnit.{1} := ForgetEnrichment.to (Complex A) X.as
  let P : Complex A := M.val.obj (op PUnit.unit)
  have hP : strictlyPerfectComplex A P := moduleFiniteCell_ringEvaluation_strictlyPerfect A hX
  refine ⟨(toHomotopy A (StrictPerfectDGComplex A)).obj
    (ForgetEnrichment.of (Complex A) ⟨P, hP⟩), ⟨eqToIso ?_⟩⟩
  change (toHomotopy A (PerfectDGModule A PUnit.{1})).obj
      (ForgetEnrichment.of (Complex A) ((strictPerfectDGComplexToPerfectDG A).obj ⟨P, hP⟩)) =
    (toHomotopy A (PerfectDGModule A PUnit.{1})).obj (ForgetEnrichment.of (Complex A) M)
  apply congrArg (fun Y : PerfectDGModule A PUnit.{1} =>
    (toHomotopy A (PerfectDGModule A PUnit.{1})).obj (ForgetEnrichment.of (Complex A) Y))
  apply Subtype.ext
  exact ringModule_recover A M.val

end SerrePositivity.DifferentialGraded
