module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftHomotopyInvariant
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinLeftCriterion

/-!
概要：任意の指定変換の相対左 Kan 条件と厳密化後の局所 U 余極限性の同値。
方針：局所輸送の選択不変性、端点の等式、指定変換の類の保存を合わせる。
規約：δ の単射性を要求しない。元の指定変換そのものを判定する。
使われ方：元の Kan 条件を相対 join の写像空間の制限定理へ渡す。

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

/-- 概要：端点と raw なホモトピーが等しい表示の相対左 Kan 条件は同値。
方針：図式の等式を消去し、ホモトピーの外延性で同一視する。
規約：表示だけを変更し、指定変換を選び直さない。
使われ方：相対 join の厳密な端点を元の図式へ戻す。 -/
lemma kanIsRelativeLeftKanExtension_iff_of_diagram_eq_of_h_eq {K C D E : SSet.{u}}
    (U : D ⟶ E) (δ : K ⟶ C) {F₀ F₀' : K ⟶ D} {F F' : C ⟶ D}
    (h₀ : F₀ = F₀') (hF : F = F')
    (α : SSet.Homotopy F₀ (δ ≫ F)) (β : SSet.Homotopy F₀' (δ ≫ F')) (h : α.h = β.h) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀ F α ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀' F' β := by
  subst F₀' F'
  have he : α = β := by
    apply SSet.RelativeMorphism.Homotopy.ext
    exact h
  subst β
  rfl

/-- 概要：相対 join の標準指定変換の相対左 Kan 条件は局所 U 余極限性と同値。
方針：局所輸送の選択不変性で標準輸送を使い、その余錐の表示を比較する。
規約：U は inner fibration、δ は任意。
使われ方：相対 join の局所条件と元の指定変換の標準的な相対 Kan 条件の界面。 -/
lemma kanIsRelativeLeftKanExtension_relativeJoin_iff_local_relativeColimits
    {K C D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) [InnerFibration U] (δ : K ⟶ C) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl δ (𝟙 C) ≫ G)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) ≫ G) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinTransformation δ G) ↔
      ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinDiagramCocone δ c G) := by
  constructor
  · intro h c
    obtain ⟨t, ht⟩ := h c
    have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_isRelativeColimit_iff U t
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeTransport δ G c)).1 ht
    rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeTransport_cocone] at hs
  · intro h c
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeTransport δ G c, ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeTransport_cocone]
    exact h c

/-- 概要：元の指定変換の相対左 Kan 条件を厳密化後の局所 U 余極限性で判定する。
方針：指定変換の類の保存、端点の厳密な等式、標準相対 join の判定を合成する。
規約：指定変換の類だけでなく、元の変換に対する条件として述べる。
使われ方：任意の指定変換から局所相対普遍図式の制限定理への還元。 -/
lemma kanRelativeLeftStrictification_iff_local_relativeColimits {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β} (r : s.Strictification) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀ F β ↔
      ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinDiagramCocone δ c r.diagram) := by
  have he := kanIsRelativeLeftKanExtension_iff_of_diagram_eq_of_h_eq U δ r.left_eq r.right_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinTransformation δ r.diagram) r.transformation (by rfl)
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtension_iff_of_homMk_eq U δ F₀ F
    r.transformation β r.transformation_hom_eq
  exact hh.symm.trans (he.symm.trans
    (kanIsRelativeLeftKanExtension_relativeJoin_iff_local_relativeColimits U δ r.diagram))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
