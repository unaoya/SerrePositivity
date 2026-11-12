module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.UniverseHomotopyReflection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.RepresentableLimitCriterion

/-!
概要：指定三形状の native な ∞ 極限性と元の q_x の同値性の同値。
方針：切断比較の後合成を消去し、ULift と反転を戻して元の比較射を得る。
規約：Hom 錐の厳密極限性や追加の比較同値を要求しない。
使われ方：HTT 4.2.4.1 の限定形、Kerodon 7.5.4.6（Tag 03BB）、γ3b の元の比較射による判定。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：反転 end からの切断比較が同値なら反転した strict 錐の合成の同値性は q′ で検出できる。
方針：後合成の同値性を消去し、ULift によるホモトピー逆の検出を使う。
規約：一般の添字圏では end の切断比較の同値性を明示する。
使われ方：三形状の native な極限性から元の q_x を戻す中間判定。 -/
lemma reflectedStrictConeSectionsComparison_homotopyEquivalence_iff {F : I ⥤ C}
    (c : Cone F) (x : C)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison c x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c x) := by
  have : ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)
  constructor
  · intro h
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ulift_homotopyEquivalence_iff _).mp
    exact hE.cancel_right h
  · intro h
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence h).comp hE

/-- 概要：離散図式の実際の錐の ∞ 極限性は全ての元の q_x の同値性と同値。
方針：native な切断判定から q′ を戻し、反転比較と元の比較の同値を使う。
規約：添字の有限性・非空性や Hom 錐の厳密極限性は要求しない。
使われ方：γ3b の積の両向きの homotopy 極限判定。 -/
lemma strictCoherentCone_isLimit_iff_discrete_representableComparison {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ x : C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) := by
  constructor
  · intro h x
    apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.representableComparison_reflection_discrete_iff c x).mpr
    apply (reflectedStrictConeSectionsComparison_homotopyEquivalence_iff c x
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_discrete_homotopyEquivalence F x)).mp
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison c).mp h x
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_of_discrete_representableComparison c

/-- 概要：Hom の一脚が fibration の cospan の ∞ 極限性は全ての元の q_x の同値性と同値。
方針：反転 end の切断比較を消去して q′ を戻し、元の比較の同値判定を使う。
規約：Hom の右脚の fibration 性や Hom 錐の厳密極限性は要求しない。
使われ方：γ3b の引き戻しの両向きの homotopy 極限判定。 -/
lemma strictCoherentCone_isLimit_iff_cospan_representableComparison
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F)
    [∀ x : C, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ x : C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) := by
  constructor
  · intro h x
    apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.representableComparison_reflection_cospan_iff c x).mpr
    apply (reflectedStrictConeSectionsComparison_homotopyEquivalence_iff c x
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_cospan_homotopyEquivalence F x)).mp
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison c).mp h x
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_representableComparison c

/-- 概要：Hom が fibration の塔をなす図式の ∞ 極限性は全ての元の q_x の同値性と同値。
方針：native な切断判定の同値性を ULift と反転の検出で元の比較へ戻す。
規約：全隣接遷移の Hom の fibration 性だけを要求し、Hom 錐の厳密極限性は要求しない。
使われ方：γ3b の塔の両向きの homotopy 極限判定。 -/
lemma strictCoherentCone_isLimit_iff_tower_representableComparison
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F)
    [∀ (x : C) (n : ℕ), Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ x : C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) := by
  constructor
  · intro h x
    apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.representableComparison_reflection_tower_iff c x).mpr
    apply (reflectedStrictConeSectionsComparison_homotopyEquivalence_iff c x
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_tower_homotopyEquivalence F x)).mp
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison c).mp h x
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_of_tower_representableComparison c

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
