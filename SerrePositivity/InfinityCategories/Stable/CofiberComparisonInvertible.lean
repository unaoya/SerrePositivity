module
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyInvertible
public import SerrePositivity.InfinityCategories.Stable.PushoutComparisonInvertible
public import SerrePositivity.InfinityCategories.Stable.CofiberSquareHomotopy

/-! # 同型な最初の二成分からの cofiber 図式の同型

概要：cofiber 図式の最初の二成分が同型なら、指定した比較ホモトピー全体も可逆である。
方針：span の第一枝の両端と、終対象へ向かう第二枝で可逆性を判定する。
規約：安定性は不要。使われ方：同型射の cofiber の消滅。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cofiber 図式間の比較で指定した最初の二つの道が可逆なら、全体も可逆。
方針：二枝の可逆性で span の可逆性を示し、押し出しの普遍性で全体へ反映する。
規約：追加の安定性を仮定しない。使われ方：cofiber の同型不変性。 -/
lemma cofiberSquareHomotopy_isInvertible_of_vertexPaths {X : SSet.{u}} [Quasicategory X]
    (t d : ZeroTriangle X) (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (Q : SSet.Homotopy t.square d.square)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex t.square 0 0) (squareVertex d.square 0 0))
    (b : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex t.square 1 0) (squareVertex d.square 1 0))
    (ha : IsInvertibleEdge a) (hb : IsInvertibleEdge b)
    (h₀ : ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ Q.h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm a.edge)
    (h₁ : ((stdSimplex.δ (0 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ Q.h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm b.edge) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy Q) := by
  let H := stableHomotopyPrecomp spanSquareBoundary Q
  let L := stableHomotopyPrecomp horn₂₀.ι₀₁ H
  let R := stableHomotopyPrecomp horn₂₀.ι₀₂ H
  have hL : L.h = (squareBottomEdge ▷ (Δ[1] : SSet.{u})) ≫ Q.h := by
    change (horn₂₀.ι₀₁ ▷ (Δ[1] : SSet.{u})) ≫
      ((spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ Q.h) = _
    rw [← Category.assoc, ← comp_whiskerRight, spanSquareBoundary_bottomEdge]
  have hR : R.h = (squareLeftEdge ▷ (Δ[1] : SSet.{u})) ≫ Q.h := by
    change (horn₂₀.ι₀₂ ▷ (Δ[1] : SSet.{u})) ≫
      ((spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫ Q.h) = _
    rw [← Category.assoc, ← comp_whiskerRight, spanSquareBoundary_leftEdge]
  have hLi : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy L) := by
    apply arrowHomotopy_isInvertible_of_endpointPaths L a b ha hb
    · rw [hL, ← Category.assoc, ← comp_whiskerRight]
      exact h₀
    · rw [hL, ← Category.assoc, ← comp_whiskerRight]
      exact h₁
  have hterm (s : ZeroTriangle X) : IsTerminalVertex
      ((horn₂₀.ι₀₂ ≫ pushoutSpan s.square).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]
    exact s.zero_corner.2
  have hRi : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy R) := by
    apply arrowHomotopy_isInvertible_of_sourcePath_terminal_targets R (hterm t) (hterm d) a ha
    rw [hR, ← Category.assoc, ← comp_whiskerRight]
    have hs : stdSimplex.δ (1 : Fin 2) ≫ squareLeftEdge.{u} =
        stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge := by
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    rw [hs]
    exact h₀
  apply pushoutSquareHomotopy_isInvertible_of_span t.square d.square ht hd Q
  exact spanHomotopy_isInvertible_of_branches H L R rfl rfl hLi hRi

/-- 概要：最初の二つの可逆な道の可換式は、全体が可逆な cofiber 図式の比較へ延長できる。
方針：既存の比較ホモトピーの延長に可逆性の判定を適用する。
規約：入力の道の一次単体を保つ。使われ方：同型射と恒等射の cofiber の比較。 -/
lemma exists_invertibleCofiberSquareHomotopy_of_comm {X : SSet.{u}} [Quasicategory X]
    (t d : ZeroTriangle X) (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex t.square 0 0) (squareVertex d.square 0 0))
    (b : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex t.square 1 0) (squareVertex d.square 1 0))
    (ha : IsInvertibleEdge a) (hb : IsInvertibleEdge b)
    (h : squareHoBottom t.square ≫ SSet.Truncated.HomotopyCategory.homMk b =
      SSet.Truncated.HomotopyCategory.homMk a ≫ squareHoBottom d.square) :
    ∃ Q : SSet.Homotopy t.square d.square,
      ((stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ Q.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm a.edge ∧
      ((stdSimplex.δ (0 : Fin 2) ≫ squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ Q.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm b.edge ∧
      IsInvertibleEdge (functorEdgeOfSimplicialHomotopy Q) := by
  obtain ⟨Q, h₀, h₁⟩ := exists_cofiberSquareHomotopy_of_comm t d ht hd a b h
  exact ⟨Q, h₀, h₁, cofiberSquareHomotopy_isInvertible_of_vertexPaths t d ht hd Q a b ha hb h₀ h₁⟩

end SerrePositivity.InfinityCategories
