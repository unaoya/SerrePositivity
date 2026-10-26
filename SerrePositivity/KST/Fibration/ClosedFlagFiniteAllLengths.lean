module
public import SerrePositivity.KST.Fibration.ClosedFlagFiniteEquivalence
public import SerrePositivity.KST.Fibration.Relative.ClosedRealizationPullback
public import SerrePositivity.KST.Fibration.FinEmptyProductIso

/-!
概要：零長を含む P 相対全有限旗の元の有限積比較は全正反復で局所化同型。
方針：K-B2 の元の零長評価同型と、同じ正長比較の共通帰納を合成する。
規約：零長同型を複製せず読み取り専用で消費する。
使われ方：全自然性四角形の実初期評価比較の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B)

/-- 概要：元の零長有限旗比較は空積を含めて全反復で実同型。
方針：元の零長評価同型を消費し、同じ空有限積の同型を消去する。
規約：K-B2 の零長 API を複製しない。使われ方：全長比較の零長初段。 -/
theorem closedFlagFiniteComparison_zero_isIso (r : ℕ) :
    IsIso (closedFlagFiniteComparison P 0 r) := by
  have : IsIso ((multiRealizationFunctor r).map (closedFlagVertex P ⦋0⦌ 0)) := by
    rw [← closedFlagZeroIso_hom]
    infer_instance
  have he : closedFlagFiniteComparison P 0 r ≫
      (finEmptyProductIso ((multiRealizationFunctor r).obj B)
        ((multiRealizationFunctor r).obj (closedStableModel P))).hom =
          (multiRealizationFunctor r).map (closedFlagVertex P ⦋0⦌ 0) :=
    closedFlagFiniteComparison_initial P 0 r
  have : IsIso (closedFlagFiniteComparison P 0 r ≫
      (finEmptyProductIso ((multiRealizationFunctor r).obj B)
        ((multiRealizationFunctor r).obj (closedStableModel P))).hom) := by
    rw [he]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp this

/-- 概要：元の初期頂点と全 P cofiber の同じ有限比較は全長・全正反復で局所化同型。
方針：元の零長評価同型と正長の共通帰納を長さで分けて消費する。
規約：B と P のみ。使われ方：K-B2 向け全有限旗の実積座標比較。 -/
theorem closedFlagFiniteComparison_localized_isIso (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (closedFlagFiniteComparison P n (r + 1))) := by
  cases n with
  | zero =>
    have := closedFlagFiniteComparison_zero_isIso P (r + 1)
    infer_instance
  | succ n => exact closedFlagFiniteComparison_positive_localized_isIso P n r

end SerrePositivity.KST.Fibration
