module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RepresentableReflection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.StrictHomotopyLimits

/-!
概要：指定三形状の元の表現可能な比較 q_x の同値性から native な ∞ 極限錐を得る。
方針：元の比較を反転比較へ移し、宇宙を持ち上げて切断比較と合成する。
規約：Hom 錐の厳密極限性を追加の前提に置かない十分条件。
使われ方：HTT 4.2.4.1 の限定形、Kerodon 7.5.4.6（Tag 03BB）、γ3b の元の比較射による判定。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：離散図式の元の q_x が全 x で同値なら実際の錐は ∞ 極限錐。
方針：反転比較との同値判定と切断比較の同値性を native な極限判定へ渡す。
規約：添字の有限性や Hom 錐の厳密極限性は要求しない。
使われ方：積の homotopy 極限図式から coherent nerve の極限図式への移送。 -/
lemma strictCoherentCone_isLimit_of_discrete_representableComparison {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F)
    (hc : ∀ x : C, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison c).mpr
  intro x
  have : ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.representableComparison_reflection_discrete_iff c x).mp (hc x))).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_discrete_homotopyEquivalence F x)

/-- 概要：一脚が Hom で fibration の cospan の元の q_x が全 x で同値なら ∞ 極限錐。
方針：元の比較を反転比較へ移し、実際の切断比較と合成して native な判定を使う。
規約：右脚の fibration 性や Hom 錐の厳密極限性は要求しない。
使われ方：引き戻しの homotopy 極限図式から coherent nerve への移送。 -/
lemma strictCoherentCone_isLimit_of_cospan_representableComparison
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F)
    [∀ x : C, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))]
    (hc : ∀ x : C, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison c).mpr
  intro x
  have : ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.representableComparison_reflection_cospan_iff c x).mp (hc x))).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_cospan_homotopyEquivalence F x)

/-- 概要：Hom が fibration の塔をなす図式の元の q_x が全 x で同値なら ∞ 極限錐。
方針：反転比較の同値性を持ち上げ、塔の切断比較と native な極限判定へ渡す。
規約：全隣接遷移の Hom の fibration 性を要求し、Hom 錐の厳密極限性は要求しない。
使われ方：塔の homotopy 極限図式から coherent nerve の極限図式への移送。 -/
lemma strictCoherentCone_isLimit_of_tower_representableComparison
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F)
    [∀ (x : C) (n : ℕ), Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))]
    (hc : ∀ x : C, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison c).mpr
  intro x
  have : ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.representableComparison_reflection_tower_iff c x).mp (hc x))).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_tower_homotopyEquivalence F x)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
