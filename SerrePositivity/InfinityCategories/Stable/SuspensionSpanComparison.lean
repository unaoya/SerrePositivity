module
public import SerrePositivity.InfinityCategories.Core.SquareHomotopyCategory
public import SerrePositivity.InfinityCategories.Stable.TerminalSpanComparison
public import SerrePositivity.InfinityCategories.Stable.Suspension

/-! # 四角形の span から suspension の span への比較

概要：任意の四角形の始点側 span から、同じ始点の suspension の span へホモトピーを作る。
方針：四角形の二辺を端点つきの辺に直し、終対象へ向かう span の比較を使う。
規約：suspension の零角の選択は固定しない。
使われ方：cofiber の余極限対象から Σ への接続射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：端点つき左辺の一次単体は左辺の制限の Yoneda 表示に一致する。
方針：定値単体と区間の恒等単体を比較する。
規約：端点の輸送を含まない。使われ方：span の二辺の照合。 -/
lemma squareLeftArrow_edge {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (squareLeftArrow F).edge = SSet.yonedaEquiv (squareLeftEdge ≫ F) := by
  change F.app _ (_, _) = F.app _ (_, _)
  congr 1
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 概要：四角形の端点つき二辺を貼った span は元の標準 span である。
方針：ホーンの pushout の両辺を比較する。
規約：下辺を第一辺、左辺を第二辺とする。使われ方：終対象への span の比較。 -/
lemma edgeSpan_squareArrows {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    edgeSpan (squareBottomArrow F) (squareLeftArrow F) = pushoutSpan F := by
  apply horn₂₀.isPushout.hom_ext
  · rw [edgeSpan_left, pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge]
    apply SSet.yonedaEquiv.injective
    exact (SSet.yonedaEquiv.apply_symm_apply _).trans (squareBottomArrow_edge F)
  · rw [edgeSpan_right, pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]
    apply SSet.yonedaEquiv.injective
    exact (SSet.yonedaEquiv.apply_symm_apply _).trans (squareLeftArrow_edge F)

/-- 概要：任意の四角形の span から同じ始点の suspension の span へのホモトピーがある。
方針：suspension の始点の等号を二辺に移送し、零角の終対象性で span を比較する。
規約：元の四角形に普遍性は不要。使われ方：cofiber の接続射の入力図式。 -/
lemma exists_suspensionSpanComparison {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (s : SuspensionSquare (squareVertex F 0 0)) :
    ∃ H : SSet.Homotopy (pushoutSpan F) (pushoutSpan s.square),
      ((stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (squareVertex F 0 0) := by
  let g₁ : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex F 0 0) (squareVertex s.square 1 0) := {
    edge := (squareBottomArrow s.square).edge
    src_eq := (squareBottomArrow s.square).src_eq.trans s.source_eq
    tgt_eq := (squareBottomArrow s.square).tgt_eq }
  let g₂ : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex F 0 0) (squareVertex s.square 0 1) := {
    edge := (squareLeftArrow s.square).edge
    src_eq := (squareLeftArrow s.square).src_eq.trans s.source_eq
    tgt_eq := (squareLeftArrow s.square).tgt_eq }
  have hs : edgeSpan g₁ g₂ = pushoutSpan s.square := by
    apply horn₂₀.isPushout.hom_ext
    · rw [edgeSpan_left, pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge]
      apply SSet.yonedaEquiv.injective
      exact (SSet.yonedaEquiv.apply_symm_apply _).trans (squareBottomArrow_edge s.square)
    · rw [edgeSpan_right, pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]
      apply SSet.yonedaEquiv.injective
      exact (SSet.yonedaEquiv.apply_symm_apply _).trans (squareLeftArrow_edge s.square)
  have h := exists_terminalSpanComparison (squareBottomArrow F) (squareLeftArrow F)
    g₁ g₂ s.other_zero.2 s.zero_corner.2
  rw [edgeSpan_squareArrows, hs] at h
  exact h

end SerrePositivity.InfinityCategories
