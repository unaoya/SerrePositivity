module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinCoconeTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinTransformationClass

/-!
概要：元の指定変換の左 Kan 条件を、厳密化した相対 join の局所余極限性で判定する。
方針：端点の厳密な等式、指定変換の類の保存、局所輸送の同定を合わせる。
規約：大域的普遍写像性や左 Kan 拡張の存在の逆方向はこの判定に含めない。
使われ方：Kerodon Proposition 7.3.6.1（Tag 0309） の相対 join への還元の入力。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：端点の図式を等式で書き換えた同じ raw な変換は同じ左 Kan 条件を持つ。
方針：図式の等式を消去し、ホモトピーの外延性を使う。
規約：表示の変更だけを扱い、任意の類の等式による不変性とは区別する。
使われ方：厳密化の端点の等式を、標準変換の型へ反映する。 -/
lemma isLeftKanExtension_iff_of_diagram_eq_of_h_eq {K C D : SSet.{u}}
    (δ : K ⟶ C) {F₀ F₀' : K ⟶ D} {F F' : C ⟶ D}
    (h₀ : F₀ = F₀') (hF : F = F')
    (α : SSet.Homotopy F₀ (δ ≫ F)) (β : SSet.Homotopy F₀' (δ ≫ F'))
    (h : α.h = β.h) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F α ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀' F' β := by
  subst F₀' F'
  have he : α = β := by
    apply SSet.RelativeMorphism.Homotopy.ext
    exact h
  subst β
  rfl

/-- 概要：厳密化した相対 join の局所余錐は元の指定 β の左 Kan 条件を判定する。
方針：指定変換の類の保存と端点の書き換えを局所比較の同値へ合成する。
規約：δ の単射性は不要。各点の局所余錐そのものを判定する。
使われ方：元のデータから相対 join 上の普遍性の証明へ進む。 -/
lemma LeftKanRelativeJoinRealization.Strictification.isLeftKanExtension_iff_local_colimits
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β ↔
      ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinDiagramCocone δ c r.diagram) := by
  have he := isLeftKanExtension_iff_of_diagram_eq_of_h_eq δ r.left_eq r.right_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinTransformation δ r.diagram) r.transformation (by rfl)
  exact r.isLeftKanExtension_iff.symm.trans
    (he.symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isLeftKanExtension_relativeJoin_iff_local_colimits δ r.diagram))

/-- 概要：左 Kan 拡張は、元の変換の類を保ち全局所余錐が普遍な相対 join 表示を持つ。
方針：厳密化の存在と局所余極限性による判定を合成する。
規約：左 Kan 条件を仮定しており、極限の存在から Kan 拡張を構成する定理ではない。
使われ方：指定 β を保った相対 join による大域的普遍性の証明への還元。 -/
lemma IsLeftKanExtension.exists_relativeJoin_local_colimits {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β) :
    ∃ (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β) (r : s.Strictification),
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r.transformation) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) ∧
      ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinDiagramCocone δ c r.diagram) := by
  obtain ⟨s, ⟨r⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanRelativeJoinStrictification_exists δ F₀ F β
  exact ⟨s, r, r.transformation_hom_eq, r.isLeftKanExtension_iff_local_colimits.1 hβ⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
