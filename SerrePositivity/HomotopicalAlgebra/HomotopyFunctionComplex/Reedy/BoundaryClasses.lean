module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.MatchingRestriction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LatchingRestriction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryLifting
public import Mathlib.CategoryTheory.PEmpty
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-! # Source lifting classes on actual boundary evaluation maps

Relative matching right maps at the lower targets imply a right map on
the matching object; the direct/colimit statement is dual. No ambient
infinite completeness or degree bijection is imposed on the value category.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) (j : J)
  {C : Type u'} [Category.{v'} C] [HasFiniteLimits C] [HasFiniteColimits C]
  {F G : J ⥤ C} (τ : F ⟶ G) (left right : MorphismProperty C)
  [MorphismProperty.IsWeakFactorizationSystem left right]

include left right in
lemma matchingEvaluation_mem_right [right.RespectsIso]
    [∀ k, HasLimitsOfShape (MatchingIndex r k) C]
    (hτ : ∀ g : MatchingIndex r j, right (relativeMatchingMap r g.obj.right τ)) :
    right ((matchingEvaluation r j).map τ) := by
  have : ∀ g : MatchingIndex r j,
      HasColimitsOfShape (LatchingIndex (matchingReedy r j) g) C := fun g ↦
    hasColimitsOfShape_of_equivalence
      (equivalenceOfIsEmpty (Discrete PEmpty.{1}) (LatchingIndex (matchingReedy r j) g))
  apply limit_mem_right (matchingReedy r j)
    (Functor.whiskerLeft (matchingTarget r j) τ) left right
  intro g
  exact (right.arrow_iso_iff (relativeMatchingRestrictionIso r g τ)).mpr (hτ g)

include left right in
lemma latchingEvaluation_mem_left [left.RespectsIso]
    [∀ k, HasColimitsOfShape (LatchingIndex r k) C]
    (hτ : ∀ g : LatchingIndex r j, left (relativeLatchingMap r g.obj.left τ)) :
    left ((latchingEvaluation r j).map τ) := by
  have : ∀ g : LatchingIndex r j,
      HasLimitsOfShape (MatchingIndex (latchingReedy r j) g) C := fun g ↦
    hasLimitsOfShape_of_equivalence
      (equivalenceOfIsEmpty (Discrete PEmpty.{1}) (MatchingIndex (latchingReedy r j) g))
  apply colimit_mem_left (latchingReedy r j)
    (Functor.whiskerLeft (latchingSource r j) τ) left right
  intro g
  exact (left.arrow_iso_iff (relativeLatchingRestrictionIso r g τ)).mp (hτ g)

end SerrePositivity.Reedy

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.9.20" (partial := special) "仮定：自然数次数付き Reedy 圏、I が一対象の latching index 全体、I′ が空（Lean が強い特殊形）。結論：各相対 latching 射が left に属すれば latching colimit 間の実際の射が left に属す。left を cofibration または trivial cofibration として (a)(b) のこの特殊形に一致。任意の二つの sieve の相対 pushout 射は扱わない。"] _root_.SerrePositivity.Reedy.latchingEvaluation_mem_left
