module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Hom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderExtension

/-!
概要：指定自然変換を相対 join 上の図式で表示するための一般の比較。
方針：自然変換を写像円柱上の図式に貼り、円柱と relative join の前合成同値を使う。
規約：δ は任意。円柱全体との自然同型を保持し、端点の制限を厳密な等式とは主張しない。
使われ方：Kerodon Proposition 7.3.6.1（Tag 0309） の relative join への還元の準備。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：左 Kan の指定自然変換を貼った写像円柱上の図式。
方針：β の終端を F と δ による制限に貼る。
規約：時間は第一因子。
使われ方：指定した自然変換を保持した relative join への表示。 -/
def leftKanCylinderDiagram {K C D : SSet.{u}} (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (β : SSet.Homotopy F₀ (δ ≫ F)) : pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) δ ⟶ D :=
  pushout.desc ((β_ (Δ[1] : SSet.{u}) K).hom ≫ β.h) F (by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
    exact β.h₁)

/-- 概要：円柱全体との同型を指定した相対 join 上の表示。
方針：端点だけの独立な同型でなく、一つの円柱図式の自然同型を保持する。
規約：δ の単射性を仮定しない。
使われ方：大域的普遍性の証明で元の β との両立を追跡する。 -/
structure LeftKanRelativeJoinRealization {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)) where
  diagram : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) ⟶ D
  comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison δ ≫ diagram)
    (leftKanCylinderDiagram δ F₀ F β)

/-- 概要：任意の δ と指定自然変換は相対 join 上に円柱図式との同型つきで表示できる。
方針：円柱から relative join への前合成の同値の本質的全射性を使う。
規約：D のみ quasicategory。端点の厳密化はこの定理には含めない。
使われ方：Kerodon Proposition 7.3.6.1（Tag 0309） の一般の δ への還元の準備。 -/
lemma leftKanRelativeJoinRealization_nonempty {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)) :
    Nonempty (LeftKanRelativeJoinRealization δ F₀ F β) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison δ)).app D) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison δ D).choose.isEssentiallySurjective
  obtain ⟨v, ⟨e⟩⟩ := he (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (leftKanCylinderDiagram δ F₀ F β))
  obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).surjective v
  exact ⟨⟨G, e⟩⟩

/-- 概要：相対 join 表示の円柱部分は元の指定自然変換の prism と自然同型。
方針：一つの比較同型を写像円柱の区間部分へ制限する。
規約：prism 全体での両立を保持する。
使われ方：指定した β のクラスの追跡。 -/
def LeftKanRelativeJoinRealization.prismIso {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (s : LeftKanRelativeJoinRealization δ F₀ F β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism δ ≫ s.diagram) ((β_ (Δ[1] : SSet.{u}) K).hom ≫ β.h) := by
  have e := s.comparison.precomp (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) δ)
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inl,
    leftKanCylinderDiagram, pushout.inl_desc] using e

/-- 概要：相対 join 表示の右端は元の F と自然同型。
方針：円柱全体の比較同型を右端へ制限する。
規約：右端の厳密な一致は仮定しない。
使われ方：元の関手と大域的表示との比較。 -/
def LeftKanRelativeJoinRealization.rightIso {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (s : LeftKanRelativeJoinRealization δ F₀ F β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) ≫ s.diagram) F := by
  have e := s.comparison.precomp (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) δ)
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr,
    leftKanCylinderDiagram, pushout.inr_desc] using e

/-- 概要：相対 join 表示の左端は元の F₀ と自然同型。
方針：prism 全体の同型を零端へ制限する。
規約：左端の同型も同じ比較同型から得る。
使われ方：元の図式と相対 join 上の図式の比較。 -/
def LeftKanRelativeJoinRealization.leftIso {K C D : SSet.{u}}
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (s : LeftKanRelativeJoinRealization δ F₀ F β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl δ (𝟙 C) ≫ s.diagram) F₀ := by
  have e := s.prismIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding,
    β.h₀] using e

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
