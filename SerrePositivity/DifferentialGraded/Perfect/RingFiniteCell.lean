module
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexOperations
public import SerrePositivity.DifferentialGraded.Perfect.FiniteCell

/-! # 一対象Aの有限cellの評価は実際の有界有限射影複体

有限操作の木について帰納し、同型操作は真の複体同型として扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 一対象A上の有限cellの評価は既存のstrictlyPerfectComplexを満たす。 -/
lemma moduleFiniteCell_ringEvaluation_strictlyPerfect {S : Set PUnit.{1}}
    {M : ModuleCategory A PUnit.{1}} (hM : moduleFiniteCellOver A PUnit.{1} S M) :
    strictlyPerfectComplex A ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M) := by
  obtain ⟨c⟩ := hM
  induction c with
  | zero =>
    exact strictlyPerfectComplex_of_isZero A _
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map_isZero (moduleZero_isZero A PUnit.{1}))
  | generator x hx =>
    cases x
    exact strictlyPerfectComplex_single A (ModuleCat.of A A) 0
  | shift s c ih => exact strictlyPerfectComplex_shift ih s
  | sum c d ihc ihd => exact strictlyPerfectComplex_biprod ihc ihd
  | cone c d f ihc ihd =>
    exact strictlyPerfectComplex_mappingCone A
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map f) ihc ihd
  | iso c e ih =>
    exact strictlyPerfectComplex_of_iso A ((moduleEvaluation A PUnit.{1} PUnit.unit).mapIso e) ih

end SerrePositivity.DifferentialGraded
