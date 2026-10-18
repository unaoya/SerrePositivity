module
public import SerrePositivity.InfinityCategories.Stable.HomotopyOppositeEdges
public import SerrePositivity.InfinityCategories.Stable.ZeroSourceCoproduct
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # 終対象終点の引き戻しの二項積性

概要：終点が終対象の引き戻しの下辺・左辺は h C の二項積の射影となる。
方針：反対四角形の二項余積を反対ホモトピー圏の比較同値で輸送する。
規約：安定性は不要。使われ方：零 cofiber の同型判定と双積の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：終点が終対象の引き戻しの下辺・左辺は h C の普遍二項錐となる。
方針：双対四角形を二項余積とし、その類を反対ホモトピー圏の同値で送る。
規約：値域は quasicategory、安定性は不要。使われ方：引き戻しの射影の同型判定。 -/
def terminalTargetPullback_isBinaryProduct {X : SSet.{u}} [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPullbackSquare R)
    (hz : IsTerminalVertex (squareVertex R 1 1)) :
    IsLimit (BinaryFan.mk (squareHoBottom R) (squareHoLeft R)) := by
  have hz' : IsInitialVertex (squareVertex (dualSquare R) 0 0) := by
    rw [dualSquare_vertex]
    exact hz.op_isInitialVertex
  let hc := zeroSourcePushout_isBinaryCoproduct (dualSquare R)
    ((isPullbackSquare_iff_dualSquare R).1 hR) hz'
  have hm := mapIsColimitOfPreservesOfIsColimit (homotopyOppositeEquivalence X).functor
    (squareHoRight (dualSquare R)) (squareHoTop (dualSquare R)) hc
  change IsColimit (BinaryCofan.mk
    ((homotopyOppositeEquivalence X).functor.map
      (SSet.Truncated.HomotopyCategory.homMk (squareRightArrow (dualSquare R))))
    ((homotopyOppositeEquivalence X).functor.map
      (SSet.Truncated.HomotopyCategory.homMk (squareTopArrow (dualSquare R))))) at hm
  rw [homotopyOppositeEquivalence_map_homMk, homotopyOppositeEquivalence_map_homMk,
    edgeUnop_dualSquare_right, edgeUnop_dualSquare_top] at hm
  exact BinaryCofan.IsColimit.unop hm

/-- 概要：上側二頂点が終対象である引き戻しの下辺は h C の同型となる。
方針：終対象を第二因子とする二項積の第一射影の同型性を使う。
規約：安定性や零射は不要。使われ方：cofiber が零である射の同型判定。 -/
lemma isIso_squareHoBottom_of_pullback_terminal_top {X : SSet.{u}} [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPullbackSquare R)
    (h₀ : IsTerminalVertex (squareVertex R 0 1))
    (h₁ : IsTerminalVertex (squareVertex R 1 1)) : IsIso (squareHoBottom R) :=
  (BinaryFan.isLimit_iff_isIso_fst h₀.isTerminalHo
    (BinaryFan.mk (squareHoBottom R) (squareHoLeft R))).1
      ⟨terminalTargetPullback_isBinaryProduct R hR h₁⟩

end SerrePositivity.InfinityCategories
