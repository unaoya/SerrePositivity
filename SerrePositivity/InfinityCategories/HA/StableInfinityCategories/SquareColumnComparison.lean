module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareHorizontalComponents
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalArrowComparison

/-! # 終対象への列の比較

概要：四角形の右の列から同じ始点の suspension の左の列へ比較できる。
方針：終対象への辺の始点固定比較を、横に一定な図式へ引き戻す。
規約：元の四角形の普遍性を使わない。
使われ方：S4 の接続射の後の零合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：四角形の右辺から指定 suspension の左辺への始点固定の比較がある。
方針：suspension の始点の表示を移し、その左上の零頂点の終対象性を使う。
規約：元の四角形の普遍性は不要。使われ方：比較の中間の列。 -/
lemma exists_squareRightToSuspensionLeft {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0)) :
    ∃ H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ s.square),
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0) := by
  let g : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 1) := {
    edge := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow s.square).edge
    src_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow s.square).src_eq.trans s.source_eq
    tgt_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow s.square).tgt_eq }
  have hf : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow F).edge = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _
  have hg : SSet.yonedaEquiv.symm g.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ s.square := by
    change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow s.square).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_edge]
    exact SSet.yonedaEquiv.symm_apply_apply _
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_terminalArrowComparison (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow F) g s.zero_corner.2
  rw [hf, hg] at he
  exact he

/-- 概要：始点固定の辺のホモトピーは、横に一定な四角形にしても始点で恒等射を与える。
方針：正方形の左下の縦座標が区間の零端点であることを使う。
規約：Arrow の等号で端点の輸送を含める。使われ方：比較の始点成分の合成。 -/
lemma squareColumnHomotopy_source_arrow {X : SSet.{u}} {f g : (Δ[1] : SSet.{u}) ⟶ X}
    (H : SSet.Homotopy f g) (x : X _⦋0⦌)
    (hH : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      snd Δ[0] Δ[1] ≫ SSet.const x) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (snd (Δ[1] : SSet.{u}) Δ[1]) H)))) =
          Arrow.mk (𝟙 (SSet.HomotopyCategory.mk x)) := by
  have hi : (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ≫
      snd (Δ[1] : SSet.{u}) Δ[1] = stdSimplex.δ (1 : Fin 2) := by
    apply SSet.yonedaEquiv.injective
    apply stdSimplex.ext
    intro j
    fin_cases j; rfl
  have hfix : ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (snd (Δ[1] : SSet.{u}) Δ[1]) H).h =
        snd Δ[0] Δ[1] ≫ SSet.const x := by
    change _ ≫ ((snd (Δ[1] : SSet.{u}) Δ[1] ▷ (Δ[1] : SSet.{u})) ≫ H.h) = _
    rw [← Category.assoc, ← comp_whiskerRight, hi]
    exact hH
  have hp : SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0 := by
    apply Prod.ext <;> decide
  have ha := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTrans_fixedVertex_arrow
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (snd (Δ[1] : SSet.{u}) Δ[1]) H).h
    (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) x hfix
  rw [hp] at ha
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (snd (Δ[1] : SSet.{u}) Δ[1]) H) _).trans ha

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
