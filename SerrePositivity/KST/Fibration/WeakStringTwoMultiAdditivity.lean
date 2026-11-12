module
public import SerrePositivity.KST.Fibration.ComposableWeakMultiStepEquivalence
public import SerrePositivity.KST.Fibration.ComposableWeakTwoFactor

/-! # 元の二辺 W 列の有限積比較の全正有限反復での同値性 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 接続した二辺の元の初期頂点・両 cofiber 比較は全正有限反復で局所化同型。 -/
theorem composableWeakTwoComparison_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (composableWeakTwoComparison q (r + 1))) :=
  composableWeakTwoComparison_localized_isIso_of_step q r
    (composableWeakMultiStep_localized_isIso q r)

/-- 元の二辺 W 列の初期頂点と両連続 cofiber の有限積比較は全正有限反復で局所化同型。 -/
theorem weakStringFiniteComparison_two_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (weakStringFiniteComparison q 2 (r + 1))) :=
  (weakStringFiniteComparison_two_localized_isIso_iff q r).2
    (composableWeakTwoComparison_localized_isIso q r)

end SerrePositivity.KST.Fibration
