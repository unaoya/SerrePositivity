module
public import SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningBaseChangeVertex
import SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningBaseChangeVertex
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeRestriction

/-! # 大域底変換の任意の実頂点で、同じ零単体上の指定比較を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 実底頂点 d での大域成分は、その同じ d の零単体上の元の制限比較。 -/
theorem leftStraighteningSectionJointDiagram_baseChangeIso_vertex [Quasicategory D]
    (d : D _⦋0⦌) :
    HEq (functorHomEvaluate (leftStraighteningSectionJointDiagram_baseChangeIso k).hom
      (ULift.up d))
      (functorHomEvaluate (straighteningJointBaseChangeRestrictionIso k).hom
        (ULift.up (nerveVertex (transportSimplexIndex d)))) := by
  have h := leftStraighteningSectionJointDiagram_baseChangeIso_value k
    (transportSimplexIndex d)
  have hp {x y : D _⦋0⦌} (he : x = y) :
      HEq (functorHomEvaluate (leftStraighteningSectionJointDiagram_baseChangeIso k).hom
        (ULift.up x))
        (functorHomEvaluate (leftStraighteningSectionJointDiagram_baseChangeIso k).hom
          (ULift.up y)) := by
    cases he
    rfl
  exact (hp (firstVertex_zeroSimplex d).symm).trans (heq_of_eq h)

end SerrePositivity.KST.Fibration
