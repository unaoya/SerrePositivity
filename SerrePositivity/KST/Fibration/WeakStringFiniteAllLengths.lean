module
public import SerrePositivity.KST.Fibration.WeakStringFiniteEquivalence
public import SerrePositivity.KST.Fibration.WeakStringZeroEquivalence
public import SerrePositivity.KST.Fibration.FinEmptyProductIso

/-! # 零長を含む同じ有限 W 列比較の全正有限反復での同値性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 零長の元の有限比較の初期成分は、全反復で厳密な同型。 -/
lemma weakStringFiniteComparison_zero_initial_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    IsIso ((multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋0⦌ 0)) := by
  change IsIso ((multiRealizationFunctor r).map (weakStringZeroExactIso q).hom)
  infer_instance

/-- 零長の元の有限比較自体も、空有限積を含めて全反復で厳密な同型。 -/
theorem weakStringFiniteComparison_zero_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) : IsIso (weakStringFiniteComparison q 0 r) := by
  have := weakStringFiniteComparison_zero_initial_isIso q r
  have he : weakStringFiniteComparison q 0 r ≫
      (finEmptyProductIso ((multiRealizationFunctor r).obj
        (closedStableModel (ClosedStablePredicate.top (sInputModel B))))
        ((multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q)))).hom =
          (multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋0⦌ 0) :=
    weakStringFiniteComparison_initial q 0 r
  have : IsIso (weakStringFiniteComparison q 0 r ≫
      (finEmptyProductIso ((multiRealizationFunctor r).obj
        (closedStableModel (ClosedStablePredicate.top (sInputModel B))))
        ((multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q)))).hom) := by
    rw [he]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp this

/-- 元の初期頂点と全連続 cofiber の比較は、零長を含む全長・全正有限反復で局所化同型。 -/
theorem weakStringFiniteComparison_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (weakStringFiniteComparison q n (r + 1))) := by
  cases n with
  | zero =>
    have := weakStringFiniteComparison_zero_isIso q (r + 1)
    infer_instance
  | succ n => exact weakStringFiniteComparison_positive_localized_isIso q n r

end SerrePositivity.KST.Fibration
