module
public import SerrePositivity.DifferentialGraded.Module.LeftEquivalence
public import SerrePositivity.DifferentialGraded.Module.Zero
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # 左dg加群圏の零対象と評価による零性の保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存左右同値から得られる左加群の具体的零対象。 -/
def leftModuleZero : LeftModuleCategory A D :=
  (leftRightOppositeEquivalence A D).inverse.obj (moduleZero A Dᵒᵖ)

lemma leftModuleZero_isZero : IsZero (leftModuleZero A D) := by
  apply IsZero.of_full_of_faithful_of_isZero (leftModuleToRightOpposite A D)
  exact (moduleZero_isZero A Dᵒᵖ).of_iso
    ((leftRightOppositeEquivalence A D).counitIso.app (moduleZero A Dᵒᵖ))

instance leftModuleHasZeroObject : HasZeroObject (LeftModuleCategory A D) :=
  (leftModuleZero_isZero A D).hasZeroObject

instance leftModuleEvaluationAdditive (x : D) : (leftModuleEvaluation A D x).Additive := by
  change ((leftModuleEvaluationDG A D x).onClosed ⋙ closedToComplex A).Additive
  infer_instance

lemma leftModuleZero_evaluation_isZero (x : D) :
    IsZero ((leftModuleEvaluation A D x).obj (leftModuleZero A D)) :=
  (leftModuleEvaluation A D x).map_isZero (leftModuleZero_isZero A D)

end SerrePositivity.DifferentialGraded
