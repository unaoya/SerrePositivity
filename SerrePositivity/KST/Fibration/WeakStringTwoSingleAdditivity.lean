module
public import SerrePositivity.KST.Fibration.ComposableWeakTwoFactor

/-! # 元の二辺の有限積比較の単回実現における加法性同値 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 接続した二辺の元の初期頂点・両 cofiber の単回実現比較は局所化同型。 -/
theorem composableWeakTwoComparison_one_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (composableWeakTwoComparison q 1)) :=
  composableWeakTwoComparison_localized_isIso_of_step q 0
    (composableWeakMultiStep_one_localized_isIso q)

/-- 元の二辺 W 列の初期頂点と両連続 cofiber の有限積比較は、単回実現で局所化同型。 -/
theorem weakStringFiniteComparison_two_one_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (weakStringFiniteComparison q 2 1)) :=
  (weakStringFiniteComparison_two_localized_isIso_iff q 0).2
    (composableWeakTwoComparison_one_localized_isIso q)

end SerrePositivity.KST.Fibration
