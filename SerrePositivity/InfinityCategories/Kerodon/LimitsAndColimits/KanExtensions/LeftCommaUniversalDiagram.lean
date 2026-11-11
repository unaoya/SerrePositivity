module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaInclusionHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinTransformationClass

/-!
概要：comma の標準変換を一度だけ底 C の中で厳密化する普遍図式。
方針：標準変換を相対 join で表示し、両端を厳密に固定した表示を選ぶ。
規約：選択は C と δ のみに依存し、標的 D や個々の関手には依存しない。
使われ方：図式の族を関手圏の単体写像として比較するための前合成射。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：comma の標準変換を恒等関手への変換として表示する。
方針：終点の恒等射との合成だけを等式で同一視する。
規約：raw なホモトピーは元の標準変換と同じ。
使われ方：底 C における普遍的な相対 join 厳密化の入力。 -/
def kanLeftCommaUniversalHomotopy {K C : SSet.{u}} (δ : K ⟶ C) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ ≫ 𝟙 C) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy δ).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy δ).h₀
  h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy δ).h₁.trans (Category.comp_id _).symm
  rel := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaHomotopy δ).rel

/-- 概要：底 C の標準変換の相対 join 表示と両端固定の厳密化を選ぶ。
方針：既存の存在定理に古典的選択を適用する。
規約：標的の変更前に一度だけ選択する。
使われ方：すべての標的への後合成で同じ図式を用いる。 -/
def kanLeftCommaUniversalStrictification {K C : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) :
    Σ s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ δ) (𝟙 C) (kanLeftCommaUniversalHomotopy δ), s.Strictification :=
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanRelativeJoinStrictification_exists (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ δ) (𝟙 C) (kanLeftCommaUniversalHomotopy δ)
  ⟨Classical.choose h, Classical.choice (Classical.choose_spec h)⟩

/-- 概要：comma の元の頂点から底の頂点への普遍的な相対 join 図式。
方針：底 C の中で選んだ厳密化の図式を使う。
規約：左端は元の頂点の δ による像、右端は C の恒等射。
使われ方：通常の関手圏から comma の相対 join の関手圏への単体写像。 -/
def kanLeftCommaUniversalDiagram {K C : SSet.{u}} [Quasicategory C] (δ : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ⟶ C :=
  (kanLeftCommaUniversalStrictification δ).2.diagram

/-- 概要：普遍図式の左端は元の頂点の像。
方針：選んだ厳密化の左端の等式を使う。
規約：単体集合の射の厳密な等式。
使われ方：関手の元の図式への制限を比較する。 -/
lemma kanLeftCommaUniversalDiagram_inl {K C : SSet.{u}} [Quasicategory C] (δ : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ kanLeftCommaUniversalDiagram δ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ δ :=
  (kanLeftCommaUniversalStrictification δ).2.left_eq

/-- 概要：普遍図式の右端は底の恒等射。
方針：選んだ厳密化の右端の等式を使う。
規約：後合成した任意の関手を右端から厳密に回収する。
使われ方：元の関手の族を保つ前合成比較の切断。 -/
lemma kanLeftCommaUniversalDiagram_inr {K C : SSet.{u}} [Quasicategory C] (δ : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ kanLeftCommaUniversalDiagram δ = 𝟙 C :=
  (kanLeftCommaUniversalStrictification δ).2.right_eq

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
