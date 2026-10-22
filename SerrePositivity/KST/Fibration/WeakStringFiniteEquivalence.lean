module
public import SerrePositivity.KST.Fibration.WeakStringFiniteRecursion
public import SerrePositivity.KST.Fibration.WeakStringFiniteComparisonOne

/-! # 全ての正有限長の W 列の同じ有限積比較は全正有限反復で局所化同型 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 先行列の元の有限積比較の同値性は、最後の cofiber の比較を通して次の長さへ移る。 -/
lemma weakStringFiniteComparison_localized_isIso_succ {B C : StableCategory.{u}}
    (q : ExactMap B C) (n r : ℕ)
    (h : IsIso (AnodyneHomotopy.anodyneQ.map
      (weakStringFiniteComparison q (n + 1) (r + 1)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (weakStringFiniteComparison q (n + 2) (r + 1))) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := weakStringTailMultiStep_localized_isIso q n r
  have := AnodyneHomotopy.whiskerRight_anodyneQ_isIso
    (weakStringFiniteComparison q (n + 1) (r + 1)) h
    ((multiRealizationFunctor (r + 1)).obj (closedStableModel (kernelClosedPredicate q)))
  have he := congrArg Q.map (weakStringFiniteComparison_factor q n (r + 1))
  have hi : IsIso (Q.map (weakStringFiniteComparison q (n + 2) (r + 1)) ≫
      Q.map (𝟙 _ ⊗ₘ (finSnocProductIso ((multiRealizationFunctor (r + 1)).obj
        (closedStableModel (kernelClosedPredicate q))) (n + 1)).hom)) := by
    rw [← Q.map_comp, ← he, Q.map_comp, Q.map_comp]
    change IsIso (Q.map (weakStringTailMultiStep q n (r + 1)) ≫
      Q.map (weakStringFiniteComparison q (n + 1) (r + 1) ▷ _) ≫ Q.map (α_ _ _ _).hom)
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

/-- 元の初期頂点と全連続 cofiber による有限比較は、全正有限長・全正有限反復で同値。 -/
theorem weakStringFiniteComparison_positive_localized_isIso {B C : StableCategory.{u}}
    (q : ExactMap B C) (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (weakStringFiniteComparison q (n + 1) (r + 1))) := by
  induction n with
  | zero => exact weakStringFiniteComparison_one_localized_isIso q r
  | succ n ih => exact weakStringFiniteComparison_localized_isIso_succ q n r ih

end SerrePositivity.KST.Fibration
