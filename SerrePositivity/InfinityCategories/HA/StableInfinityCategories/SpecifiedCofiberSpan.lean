module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanZeroBranchIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitDiagramIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSpanComparison

/-! # 指定した零枝を持つ span の余極限

概要：安定 ∞ 圏で、第二枝が指定した終対象へ向かう span は余極限を持つ。
方針：第一枝の選ばれた cofiber の span と同型にし、余極限の存在を輸送する。
規約：終対象やそこへの辺の選択を入力のまま保つ。使われ方：懸垂と零射からの有限直和の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：第二枝が終対象へ向かう指定された span は余極限を持つ。
方針：第一枝の cofiber に付随する標準 span との同型で余極限を輸送する。
規約：安定性のみから、第二枝を指定したまま存在を得る。
使われ方：外側四角形の余極限余錐を実際に与える。 -/
lemma hasColimit_span_of_terminal_second {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₂ ≫ p).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p))
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare e
  have hfirst : horn₂₀.ι₀₁ ≫ p = horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge, s.bottom_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    exact s.zero_corner.2
  obtain ⟨i⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_functorIso_span_of_first_eq_terminal_second
    p (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square) hfirst hz hs
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_functorIso i).2 ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square, s.isPushout⟩

/-- 概要：第二枝が指定した零頂点へ向かう span は余極限を持つ。
方針：零頂点の終対象性を使う。
規約：入力の span 全体を保持する。使われ方：指定した零枝の cofiber。 -/
lemma hasColimit_span_of_zero_second {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((horn₂₀.ι₀₂ ≫ p).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p :=
  hasColimit_span_of_terminal_second p hz.2

/-- 概要：零角を持つ任意の四角形の入力 span は余極限を持つ。
方針：第二枝の終点が指定された零角であることを使う。
規約：元の四角形の押し出し性は仮定しない。使われ方：cofiber の入力を固定した構成。 -/
lemma hasColimit_pushoutSpan_of_zeroTriangle {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan t.square) := by
  apply hasColimit_span_of_zero_second
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
  exact t.zero_corner

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
