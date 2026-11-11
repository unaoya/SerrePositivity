module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightRelativeJoinEndpoints
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorIsoExtension

/-!
概要：右相対 join 表示の両端を元の図式へ同時に厳密化する。
方針：一つの円柱比較の両端同型を、単射な両端包含に沿って延長する。
規約：δ は任意、補正の実際のホモトピーを保持する。
使われ方：元の右指定変換の類を保った相対 join への還元。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：一つの右相対 join 表示の両端の同時の厳密化。
方針：両端図式の同型の延長データを使う。
規約：両端は左が F、右が F₀。
使われ方：指定変換の類の比較に使う補正ホモトピー。 -/
abbrev RightKanRelativeJoinRealization.Strictification {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorIsoExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightRelativeJoinEndpointInclusion δ) s.diagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F F₀) s.endpointsIso

/-- 概要：右相対 join 表示の両端を同時に厳密化できる。
方針：両端包含の単射性と同型の延長の一般定理。
規約：δ の単射性は不要。
使われ方：端点で元の二図式を厳密に持つ表示の構成。 -/
lemma RightKanRelativeJoinRealization.strictification_nonempty {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α) :
    Nonempty s.Strictification :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoExtension_nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightRelativeJoinEndpointInclusion δ) s.diagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F F₀) s.endpointsIso

/-- 概要：補正後の左端は元の F に厳密に等しい。
方針：両端の制限の等式を C の成分で評価する。
規約：自然同型ではなく射の等式。
使われ方：右比較錐の頂点側の図式の固定。 -/
lemma RightKanRelativeJoinRealization.Strictification.left_eq {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α}
    (r : s.Strictification) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ ≫ r.diagram = F := by
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ ≫ r.diagram =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl C K ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightRelativeJoinEndpointInclusion δ ≫ r.diagram) := rfl
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl C K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F F₀ :=
      congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl C K ≫ t) r.restriction
    _ = F := rfl

/-- 概要：補正後の右端は元の F₀ に厳密に等しい。
方針：両端の制限の等式を K の成分で評価する。
規約：左右は同じ補正で同時に固定する。
使われ方：右比較錐の制限図式の固定。 -/
lemma RightKanRelativeJoinRealization.Strictification.right_eq {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α}
    (r : s.Strictification) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ ≫ r.diagram = F₀ := by
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ ≫ r.diagram =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr C K ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightRelativeJoinEndpointInclusion δ ≫ r.diagram) := rfl
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr C K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F F₀ :=
      congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr C K ≫ t) r.restriction
    _ = F₀ := rfl

/-- 概要：補正した右相対 join 図式が与える元の両端を持つ指定変換。
方針：標準右 prism に図式を後合成し、厳密な両端の等式を使う。
規約：α との類の一致は後続の証明で導く。
使われ方：右 Kan 条件を元の指定変換から標準表示へ移す。 -/
def RightKanRelativeJoinRealization.Strictification.transformation {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α}
    (r : s.Strictification) : SSet.Homotopy (δ ≫ F) F₀ where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ ≫ r.diagram
  h₀ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism_zero, Category.assoc, r.left_eq]
    rfl
  h₁ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism_one, r.right_eq]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：任意の右指定変換には両端を厳密化した右相対 join 表示が存在する。
方針：円柱比較つき表示を取り、その一つの両端同型を延長する。
規約：この存在だけで補正後の指定変換の類が α と一致するとは主張しない。
使われ方：保持した補正の coherence から類の一致を導く。 -/
lemma rightKanRelativeJoinStrictification_exists {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanRelativeJoinRealization δ F₀ F α, Nonempty s.Strictification := by
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanRelativeJoinRealization_nonempty δ F₀ F α
  exact ⟨s, s.strictification_nonempty⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
