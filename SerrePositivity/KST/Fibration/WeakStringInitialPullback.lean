module
public import SerrePositivity.KST.Fibration.WeakStringPulledCoordinates
public import SerrePositivity.KST.Fibration.ProductCoordinatePullbackTransfer

/-! # 元の全有限 W 列の初期評価と Verdier 包含のホモトピー引き戻し -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 後合成と初期評価の元の実現射そのものの厳密な可換四角形。 -/
theorem weakStringInitialPostSquare {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    CommSq
      ((multiRealizationFunctor r).map
        (weakStringVertexTopExact (f ≫ q : A ⟶ C) ⦋n⦌ 0))
      ((multiRealizationFunctor r).map (weakStringPostExact f q ⦋n⦌))
      ((multiRealizationFunctor r).map (topPostExact f))
      ((multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋n⦌ 0)) := by
  constructor
  rw [← Functor.map_comp, ← Functor.map_comp, weakStringVertexTopExact_postcomp]

/-- Verdier 列の元の W 列の初期評価四角形は、全長・全正有限反復で homotopy pullback。 -/
theorem weakStringInitialPostSquare_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n r : ℕ) :
    IsHomotopyPullback (weakStringInitialPostSquare i q n (r + 1)) := by
  apply isHomotopyPullback_of_productCoordinates
    (weakStringInitialPostSquare i q n (r + 1))
    (weakStringFiniteComparison q n (r + 1))
    (weakStringFiniteComparison_initial q n (r + 1))
    (weakStringFiniteComparison_localized_isIso q n r)
  simpa only [weakStringFiniteComparison, weakStringPulledCoordinates, lift_snd] using
    weakStringPulledCoordinates_verdier_localized_isIso h n r

end SerrePositivity.KST.Fibration
