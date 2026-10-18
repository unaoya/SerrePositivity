module
public import SerrePositivity.InfinityCategories.Stable.TerminalArrowSourcePath
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Stable.PushoutSquareHomotopyLift

/-! # 可換正方形から cofiber 図式間のホモトピーへ

概要：cofiber 列の最初の二成分が h で可換なら、その道を保持した図式間のホモトピーがある。
方針：二つの枝のホモトピーを同じ始点の道で貼り、普遍余錐へ持ち上げる。
規約：安定性や三角圏の構造は使わない。
使われ方：S4 の TR3 の第三成分の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cofiber 列の最初の二成分の可換性は、二つの道を保持した図式の比較に延長できる。
方針：辺の比較と零頂点への比較を span に貼り、そのホモトピーを押し出し四角形へ延長する。
規約：値域は quasicategory。使われ方：TR3 の第三成分。 -/
lemma exists_cofiberSquareHomotopy_of_comm {X : SSet.{u}} [Quasicategory X]
    (t d : ZeroTriangle X) (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex t.square 0 0) (squareVertex d.square 0 0))
    (b : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex t.square 1 0) (squareVertex d.square 1 0))
    (h : squareHoBottom t.square ≫ SSet.Truncated.HomotopyCategory.homMk b =
      SSet.Truncated.HomotopyCategory.homMk a ≫ squareHoBottom d.square) :
    ∃ Q : SSet.Homotopy t.square d.square,
      ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ Q.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm a.edge ∧
      ((stdSimplex.δ (0 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ Q.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm b.edge := by
  have hf (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
      SSet.yonedaEquiv.symm (squareBottomArrow F).edge = squareBottomEdge ≫ F := by
    rw [squareBottomArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _
  have he := exists_arrowHomotopy_of_homMk_comm (squareBottomArrow t.square)
    (squareBottomArrow d.square) a b h
  rw [hf t.square, hf d.square] at he
  obtain ⟨L, hL₀, hL₁⟩ := he
  obtain ⟨R, hR₀⟩ := exists_terminalArrowHomotopy_of_sourcePath
    (squareLeftEdge ≫ t.square) (squareLeftEdge ≫ d.square) d.zero_corner.2 a
  have h₁ (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
      horn₂₀.ι₀₁ ≫ pushoutSpan F = squareBottomEdge ≫ F := by
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge]
  have h₂ (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
      horn₂₀.ι₀₂ ≫ pushoutSpan F = squareLeftEdge ≫ F := by
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]
  let L' := stableHomotopyRetarget L (h₁ t.square).symm (h₁ d.square).symm
  let R' := stableHomotopyRetarget R (h₂ t.square).symm (h₂ d.square).symm
  obtain ⟨H, hHL, _⟩ := exists_spanHomotopy_of_branchHomotopies
    (pushoutSpan t.square) (pushoutSpan d.square) L' R' (hL₀.trans hR₀.symm)
  obtain ⟨Q, hQ⟩ := exists_pushoutSquareHomotopy_lift_span t.square d.square ht hd H
  let V : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ X := Q.h
  let W : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X := L.h
  let Z : (horn 2 0 : SSet.{u}) ⊗ Δ[1] ⟶ X := H.h
  change (spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ V = Z at hQ
  change (horn₂₀.ι₀₁ ▷ (Δ[1] : SSet.{u})) ≫ Z = W at hHL
  have hbottom : (squareBottomEdge ▷ (Δ[1] : SSet.{u})) ≫ V = W := by
    rw [← spanSquareBoundary_bottomEdge, comp_whiskerRight, Category.assoc, hQ]
    exact hHL
  refine ⟨Q, ?_, ?_⟩
  · change ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ V = _
    rw [comp_whiskerRight, Category.assoc, hbottom]
    exact hL₀
  · change ((stdSimplex.δ (0 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ V = _
    rw [comp_whiskerRight, Category.assoc, hbottom]
    exact hL₁

end SerrePositivity.InfinityCategories
