module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinEndpoints
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorIsoExtension

/-!
概要：左指定自然変換の相対 join 表示の両端を元の図式に厳密化する。
方針：両端を同時に含める単射に沿い、一つの円柱比較の制限を延長する。
規約：δ は任意。指定自然変換の類の一致の導出に使う延長ホモトピーを保持する。
使われ方：Kerodon Proposition 7.3.6.1（Tag 0309） の relative join への還元。

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

/-- 概要：相対 join 表示の両端の同時の厳密化。
方針：一つの円柱比較から得た両端の同型の延長データを使う。
規約：元の相対 join 表示 s に対する補正を記録する。
使われ方：補正後の関手と元の指定自然変換の比較。 -/
abbrev LeftKanRelativeJoinRealization.Strictification {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorIsoExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinEndpointInclusion δ) s.diagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F₀ F) s.endpointsIso

/-- 概要：任意の左指定自然変換の相対 join 表示は両端を同時に厳密化できる。
方針：両端包含の単射性と同型の延長の一般定理を使う。
規約：δ 自体の単射性は仮定しない。
使われ方：元の二図式を端点で厳密に持つ相対 join 上の図式の構成。 -/
lemma LeftKanRelativeJoinRealization.strictification_nonempty {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β) :
    Nonempty s.Strictification :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoExtension_nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinEndpointInclusion δ) s.diagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F₀ F) s.endpointsIso

/-- 概要：厳密化した図式の左端は元の F₀ に厳密に等しい。
方針：両端の制限の等式を左因子で評価する。
規約：同型ではなく単体集合の射の等式。
使われ方：固定図式上の関手圏による普遍性の比較。 -/
lemma LeftKanRelativeJoinRealization.Strictification.left_eq {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β}
    (r : s.Strictification) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl δ (𝟙 C) ≫ r.diagram = F₀ := by
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl δ (𝟙 C) ≫ r.diagram =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl K C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinEndpointInclusion δ ≫ r.diagram) := rfl
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl K C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F₀ F :=
      congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl K C ≫ t) r.restriction
    _ = F₀ := rfl

/-- 概要：厳密化した図式の右端は元の F に厳密に等しい。
方針：両端の制限の等式を右因子で評価する。
規約：左右は同じ補正によって同時に固定する。
使われ方：元の関手の指定自然変換を相対 join の prism と比較する。 -/
lemma LeftKanRelativeJoinRealization.Strictification.right_eq {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β}
    (r : s.Strictification) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) ≫ r.diagram = F := by
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) ≫ r.diagram =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr K C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinEndpointInclusion δ ≫ r.diagram) := rfl
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr K C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc F₀ F :=
      congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr K C ≫ t) r.restriction
    _ = F := rfl

/-- 概要：厳密化した相対 join 上の図式は元の二図式の間の自然変換を与える。
方針：標準 prism を図式で写し、両端の厳密な等式を使う。
規約：入力 β と同じ両端を持つ。β との h での一致は後続の TransformationClass で証明する。
使われ方：元の指定自然変換と厳密化後の自然変換のクラスの比較。 -/
def LeftKanRelativeJoinRealization.Strictification.transformation {K C D : SSet.{u}}
    [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β}
    (r : s.Strictification) : SSet.Homotopy F₀ (δ ≫ F) where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism δ ≫ r.diagram
  h₀ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism δ ≫ r.diagram = F₀
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_zero, r.left_eq]
  h₁ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism δ ≫ r.diagram = δ ≫ F
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_one, Category.assoc, r.right_eq]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：任意の左指定自然変換には両端を厳密化した相対 join 表示の証明データが存在する。
方針：円柱図式の表示とその同じ比較の両端での補正を順に取る。
規約：この定理だけで補正後の prism の類が β と等しいとは主張しない。
使われ方：保持した比較ホモトピーから指定自然変換の h での一致を導く。 -/
lemma leftKanRelativeJoinStrictification_exists {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization δ F₀ F β, Nonempty s.Strictification := by
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanRelativeJoinRealization_nonempty δ F₀ F β
  exact ⟨s, s.strictification_nonempty⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
