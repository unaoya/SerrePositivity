module
public import SerrePositivity.KST.Fibration.ClosedKernelFiniteCoordinates
public import SerrePositivity.KST.Fibration.ClosedFlagCofiberPostcomparison
public import SerrePositivity.KST.Fibration.ClosedFlagFiniteAllLengths
public import SerrePositivity.KST.Fibration.ProductCoordinatePullbackTransfer
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LocalizedPairBothEquality
public import SerrePositivity.KST.Fibration.LocalizedFiniteProductEquality

/-!
概要：元の P 全旗包含と初期評価の実四角形は全長・全正反復で引き戻し。
方針：元の cofiber 係数比較で引き戻した実積座標を同じ全長比較へ戻す。
規約：B と P のみ。商・核表示・共終性・retract 閉包を使わない。
使われ方：K-B2 向け全単体的自然性の共通仕上げへの入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B)

/-- 概要：元の P 全旗包含に沿って引き戻した実 cofiber 座標。
方針：源の元の初期評価を保ち、標的の元の全連続 cofiber だけを引き戻す。
規約：同じ元の包含。使われ方：実初期評価四角形の座標立方体。 -/
def closedKernelPulledCoordinates (n r : ℕ) :=
  lift ((multiRealizationFunctor r).map (closedKernelInitialExact P ⦋n⦌))
    ((multiRealizationFunctor r).map (closedKernelFlagPost P ⦋n⦌) ≫
      closedFlagConsecutiveCofibers P n r)

/-- 概要：引き戻した元の座標は局所化後に同じ P 全旗有限比較と一致する。
方針：元の包含に沿う全 cofiber 関手同型を各元の有限積射影へ代入する。
規約：全長の元の比較写像そのもの。使われ方：引き戻した座標射の実同値性。 -/
theorem closedKernelPulledCoordinates_localized_eq (n r : ℕ) :
    AnodyneHomotopy.anodyneQ.map (closedKernelPulledCoordinates P n (r + 1)) =
      AnodyneHomotopy.anodyneQ.map (closedKernelFiniteComparison P n (r + 1)) := by
  unfold closedKernelPulledCoordinates closedKernelFiniteComparison weakStringFiniteComparison
  rw [lift_map]
  simp only [closedKernelInitialExact, Functor.map_comp]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pair_eq_of_anodyneQ_eq rfl
  apply finProduct_eq_of_anodyneQ_eq
  intro j
  simpa only [closedFlagConsecutiveCofibers, weakStringConsecutiveCofibers,
    Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π,
    weakStringCofiberMultiMap, Functor.map_comp] using
    closedFlagCofiberMultiMap_postcomp P (consecutiveWeakStringEdge n j) r

/-- 概要：同じ元の包含に沿う実座標射は全長・全正反復で局所化同型。
方針：同じ全長有限比較との局所化後の厳密一致を使う。
規約：B と P のみ。使われ方：元の初期評価四角形の引き戻し移送。 -/
theorem closedKernelPulledCoordinates_localized_isIso (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (closedKernelPulledCoordinates P n (r + 1))) := by
  rw [closedKernelPulledCoordinates_localized_eq]
  exact closedKernelFiniteComparison_localized_isIso P n r

/-- 概要：元の P 全旗包含と実初期評価の四角形は全長・全正反復で引き戻し。
方針：同じ元の実積座標を保持する既存の比較立方体の定理を消費する。
規約：商・Verdier 列・共終性は入力でない。
使われ方：全単体的な実自然性四角形の引き戻しへの共通の第一段。 -/
theorem closedKernelInitialPostSquare_homotopyPullback (n r : ℕ) :
    IsHomotopyPullback (closedKernelInitialPostSquare P ⦋n⦌ (r + 1)) := by
  apply isHomotopyPullback_of_productCoordinates
    (closedKernelInitialPostSquare P ⦋n⦌ (r + 1))
    (closedFlagFiniteComparison P n (r + 1))
    (closedFlagFiniteComparison_initial P n (r + 1))
    (closedFlagFiniteComparison_localized_isIso P n r)
  simpa only [closedFlagFiniteComparison, closedKernelPulledCoordinates, lift_snd] using
    closedKernelPulledCoordinates_localized_isIso P n r

end SerrePositivity.KST.Fibration
