module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeComparisonReflection

/-!
概要：指定三形状で元の表現可能な比較 q_x と反転した比較 q′ の同値性が一致する。
方針：実際の Hom 錐に反転比較の一般の定理を適用する。
規約：局所 Kan 性と形状に対応する Hom の fibration 性だけを要求する。
使われ方：HTT 4.2.4.1 の限定形、γ3b の元の比較射による極限判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：離散図式の任意の錐の元の q_x と反転比較 q′ の同値性が一致する。
方針：実際の Hom 錐に離散図式の反転比較を適用する。
規約：Hom 錐の厳密極限性、添字の有限性や非空性は要求しない。
使われ方：γ3b の積の元の比較射による判定。 -/
lemma representableComparison_reflection_discrete_iff {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c x) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x).pt :=
    inferInstanceAs (KanComplex (SimplicialCategory.sHom x c.pt))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_reflection_discrete_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x)

/-- 概要：一脚が Hom で fibration の cospan の元の q_x と反転比較 q′ の同値性が一致する。
方針：実際の Hom 錐に一脚 fibration の反転比較を適用する。
規約：右脚の fibration 性や Hom 錐の厳密極限性は要求しない。
使われ方：γ3b の引き戻しの元の比較射による判定。 -/
lemma representableComparison_reflection_cospan_iff
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F) (x : C)
    [Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c x) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x).pt :=
    inferInstanceAs (KanComplex (SimplicialCategory.sHom x c.pt))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_reflection_cospan_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x)

/-- 概要：Hom が fibration の塔である図式の元の q_x と反転比較 q′ の同値性が一致する。
方針：実際の Hom 錐に全隣接遷移での反転比較を適用する。
規約：Hom 錐の厳密極限性や追加の標準比較の同値性は要求しない。
使われ方：γ3b の塔の元の比較射による判定。 -/
lemma representableComparison_reflection_tower_iff
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F) (x : C)
    [∀ n : ℕ, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c x) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x).pt :=
    inferInstanceAs (KanComplex (SimplicialCategory.sHom x c.pt))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_reflection_tower_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
