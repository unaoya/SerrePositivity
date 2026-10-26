module
public import SerrePositivity.KST.Fibration.ClosedTailMultiStep
public import SerrePositivity.KST.Fibration.ClosedFlagFiniteRecursion
public import SerrePositivity.KST.Fibration.StandardTailCoordinates

/-!
概要：閉じた P 旗の相対加法性を、元の先行面と最後の連続 cofiber の実比較へ戻す。
方針：元の全旗制限の完全同値を通し、両成分を同じ実単体制限へ厳密照合する。
規約：商や核表示を使わず、補完切断を選び直さない。
使われ方：P 版の同じ有限旗比較に共通の帰納段を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ)

/-- 概要：元の全旗制限の先行成分は、元の最後の面射そのもの。
方針：同じ周囲への包含を消去し、元の実単体制限の合成を計算する。
規約：厳密回収。使われ方：有限旗比較の第一成分。 -/
theorem closedFlagTail_prefix :
    (closedFlagTailEquivalence P n).hom ≫ closedTailPrefix P n =
      closedFlagMap P (SimplexCategory.δ (Fin.last (n + 2))) := by
  apply closedStableInclusion_cancel (closedFlagStablePredicate P ⦋n + 1⦌)
  apply Subtype.ext
  have hp : (closedTailPrefix P n).val ≫
      (closedStableInclusion (closedFlagStablePredicate P ⦋n + 1⦌)).val =
        (closedStableInclusion (closedTailPredicate P n)).val ≫
          (pre (standardTailPrefix n)).app B.carrier := rfl
  have hr : (closedFlagTailRestriction P n) ≫
      (closedStableInclusion (closedTailPredicate P n)).val =
        (closedStableInclusion (closedFlagStablePredicate P ⦋n + 2⦌)).val ≫
          (pre (standardTailInclusion n)).app B.carrier := rfl
  change ((closedFlagTailRestriction P n) ≫ (closedTailPrefix P n).val) ≫ _ = _
  rw [Category.assoc, hp, ← Category.assoc, hr, Category.assoc,
    ← NatTrans.comp_app, ← pre_map, standardTailPrefix_inclusion]
  exact (congrArg (fun f => f.val) (closedFlagMap_inclusion P
    (SimplexCategory.δ (Fin.last (n + 2))))).symm

/-- 概要：元の全旗制限の最後の辺成分は元の最後の連続辺そのもの。
方針：同じ周囲への包含を消去し、指定辺の実単体制限を回収する。
規約：同じ実辺。使われ方：有限旗比較の共通 cofiber 成分。 -/
theorem closedFlagTail_edge :
    (closedFlagTailEquivalence P n).hom ≫ closedTailEdge P n =
      closedFlagEdge P (consecutiveWeakStringEdge (n + 2) (Fin.last (n + 1))) := by
  apply closedStableInclusion_cancel (closedArrowPredicate P)
  apply Subtype.ext
  have hp : (closedTailEdge P n).val ≫ (closedStableInclusion (closedArrowPredicate P)).val =
      (closedStableInclusion (closedTailPredicate P n)).val ≫
        (pre (tailAttachmentEdge (Δ[n] : SSet.{u}))).app B.carrier := rfl
  have hr : (closedFlagTailRestriction P n) ≫
      (closedStableInclusion (closedTailPredicate P n)).val =
        (closedStableInclusion (closedFlagStablePredicate P ⦋n + 2⦌)).val ≫
          (pre (standardTailInclusion n)).app B.carrier := rfl
  change ((closedFlagTailRestriction P n) ≫ (closedTailEdge P n).val) ≫ _ = _
  rw [Category.assoc, hp, ← Category.assoc, hr, Category.assoc,
    ← NatTrans.comp_app, ← pre_map, standardTailEdge_eq_consecutive]
  exact (congrArg (fun f => f.val) (closedFlagEdge_inclusion P
    (consecutiveWeakStringEdge (n + 2) (Fin.last (n + 1))))).symm

/-- 概要：同じ全旗制限は元の最後の連続 cofiber を同じ補完で厳密回収。
方針：元の辺回収へ共通切断と quotient 頂点を合成する。
規約：同じ補完選択。使われ方：全反復での実比較の第二成分。 -/
theorem closedFlagTail_cofiber :
    (closedFlagTailEquivalence P n).hom ≫ closedTailCofiber P n =
      closedFlagCofiber P (consecutiveWeakStringEdge (n + 2) (Fin.last (n + 1))) := by
  simp only [closedTailCofiber, closedFlagCofiber, closedFlagCofiberCompletion,
    ← Category.assoc, closedFlagTail_edge]

/-- 概要：全旗の元の比較段は、同じ tail 模型上の実相対加法性との合成。
方針：元の二成分の厳密回収を実現へ送る。
規約：同じ先行旗・cofiber。使われ方：共通有限旗帰納の同値入力。 -/
theorem closedFlagTailMultiStep_factor (r : ℕ) :
    (multiRealizationFunctor r).map (closedFlagTailEquivalence P n).hom ≫
      closedTailMultiStep P n r = closedFlagTailMultiStep P n r := by
  rw [closedTailMultiStep, comp_lift, ← Functor.map_comp, ← Functor.map_comp,
    closedFlagTail_prefix, closedFlagTail_cofiber]
  rfl

/-- 概要：元の全旗の先行面と最後の P cofiber の比較は全正反復で局所化同型。
方針：元の実旗制限の同値と同じ相対加法性を合成する。
規約：B と P 以外の存在仮定なし。使われ方：有限旗の共通帰納段を放電する。 -/
theorem closedFlagTailMultiStep_localized_isIso (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (closedFlagTailMultiStep P n (r + 1))) := by
  have := multiRealization_map_localized_isIso_of_equivalence r (closedFlagTailEquivalence P n)
  have := closedTailMultiStep_localized_isIso P n r
  rw [← closedFlagTailMultiStep_factor, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration
