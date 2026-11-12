module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SquareHomotopyCategory
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalSpanComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Suspension

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：端点つき左辺の一次単体は左辺の制限の Yoneda 表示に一致する。
方針：定値単体と区間の恒等単体を比較する。
規約：端点の輸送を含まない。使われ方：span の二辺の照合。 -/
lemma squareLeftArrow_edge {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow F).edge = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F) := by
  change F.app _ (_, _) = F.app _ (_, _)
  congr 1
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 概要：四角形の端点つき二辺を貼った span は元の標準 span である。
方針：ホーンの pushout の両辺を比較する。
規約：下辺を第一辺、左辺を第二辺とする。使われ方：終対象への span の比較。 -/
lemma edgeSpan_squareArrows {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow F) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow F) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F := by
  apply horn₂₀.isPushout.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    apply SSet.yonedaEquiv.injective
    exact (SSet.yonedaEquiv.apply_symm_apply _).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge F)
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    apply SSet.yonedaEquiv.injective
    exact (SSet.yonedaEquiv.apply_symm_apply _).trans (squareLeftArrow_edge F)

/-- 概要：任意の四角形の span から同じ始点の suspension の span へのホモトピーがある。
方針：suspension の始点の等号を二辺に移送し、零角の終対象性で span を比較する。
規約：元の四角形に普遍性は不要。使われ方：cofiber の接続射の入力図式。 -/
lemma exists_suspensionSpanComparison {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)) :
    ∃ H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square),
      ((stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0) := by
  let g₁ : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 0) := {
    edge := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow s.square).edge
    src_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow s.square).src_eq.trans s.source_eq
    tgt_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow s.square).tgt_eq }
  let g₂ : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 1) := {
    edge := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow s.square).edge
    src_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow s.square).src_eq.trans s.source_eq
    tgt_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow s.square).tgt_eq }
  have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan g₁ g₂ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square := by
    apply horn₂₀.isPushout.hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
      apply SSet.yonedaEquiv.injective
      exact (SSet.yonedaEquiv.apply_symm_apply _).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge s.square)
    · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
      apply SSet.yonedaEquiv.injective
      exact (SSet.yonedaEquiv.apply_symm_apply _).trans (squareLeftArrow_edge s.square)
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_terminalSpanComparison (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow F) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow F)
    g₁ g₂ s.other_zero.2 s.zero_corner.2
  rw [edgeSpan_squareArrows, hs] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
