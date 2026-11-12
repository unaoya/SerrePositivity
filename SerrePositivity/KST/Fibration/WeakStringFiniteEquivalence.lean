module
public import SerrePositivity.KST.Fibration.FiniteFlagComparisonInduction
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
lemma weakStringFiniteComparison_localized_isIso_succ {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ)
    (h : IsIso (AnodyneHomotopy.anodyneQ.map
      (weakStringFiniteComparison q (n + 1) (r + 1)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (weakStringFiniteComparison q (n + 2) (r + 1))) := by
  exact finiteFlagComparison_step_localized_isIso (n + 1)
    (weakStringFiniteComparison q (n + 1) (r + 1))
    (weakStringFiniteComparison q (n + 2) (r + 1))
    (weakStringTailMultiStep q n (r + 1))
    (weakStringFiniteComparison_factor q n (r + 1)) h
    (weakStringTailMultiStep_localized_isIso q n r)

/-- 元の初期頂点と全連続 cofiber による有限比較は、全正有限長・全正有限反復で同値。 -/
theorem weakStringFiniteComparison_positive_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (weakStringFiniteComparison q (n + 1) (r + 1))) := by
  induction n with
  | zero => exact weakStringFiniteComparison_one_localized_isIso q r
  | succ n ih => exact weakStringFiniteComparison_localized_isIso_succ q n r ih

end SerrePositivity.KST.Fibration
