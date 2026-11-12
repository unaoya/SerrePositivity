module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeWeightAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeWeightComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.RepresentableComparison

/-!
概要：Kan 複体から始まる fibration の塔の strict 極限からの標準比較はホモトピー同値。
方針：補助重みへの比較と元の重みへの制限に厳密に分解し、それぞれの同値性を合成する。
規約：既存の κ と q_x そのものを扱い、同値な別の射へ置き換えない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の塔の homotopy 極限の入力。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：塔の補助重みの end から Bousfield–Kan end への制限は trivial Kan fibration。
方針：over 圏の終対象から得た成分ごとの anodyne 性を塔の重みの制限へ渡す。
規約：零段の Kan 性と隣接遷移の Fibration 性を前提とする。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の κ の分解の第二の射。 -/
lemma bousfieldKanConeWeightInclusion_tower_trivialKanFibration
    (H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_tower_trivialKanFibration _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion_anodyne

/-- 概要：fibration の塔の極限錐からの Bousfield–Kan 標準比較はホモトピー同値。
方針：補助重みへの比較の同値性と、その end から元の重みへの制限の同値性を合成する。
規約：任意の極限錐 c を使い、その頂点の Kan 性を前提に追加しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.1（Tag 03B6） の塔の homotopy 極限錐。 -/
lemma bousfieldKanConeComparison_tower_homotopyEquivalence
    {H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (c : Cone H) (hc : IsLimit c)
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) := by
  let U := (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj (Δ[0] : SSet.{u})
  have hU : IsTerminal U := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightIsTerminalOfObj U (fun _ => stdSimplex.isTerminalObj₀)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_isIso_of_isTerminalWeight U hU c hc
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex U H
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison U c)).symm
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeight (AsSmall.{u} ℕᵒᵖ)) H
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} ℕᵒᵖ)) H
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_factorization c]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightComparison_tower_homotopyEquivalence c hc).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_tower_homotopyEquivalence (H := H)
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion_anodyne)

/-- 概要：fibration の塔の選択された strict 極限からの実際の κ はホモトピー同値。
方針：選択された極限錐に任意の極限錐の比較の定理を適用する。
規約：添字は明示的な AsSmall.{u} ℕᵒᵖ。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の表現可能な比較の κ_x。 -/
lemma bousfieldKanLimitComparison_tower_homotopyEquivalence
    (H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H) :=
  bousfieldKanConeComparison_tower_homotopyEquivalence (limit.cone H) (limit.isLimit H)

/-- 概要：豊穣極限の Hom 図式が fibration の塔なら実際の表現可能な q_x は同値。
方針：sHom で作った極限錐に塔の Bousfield–Kan 比較を直接適用する。
規約：Hom 図式の極限性、零段の Kan 性と隣接遷移の Fibration 性を省略しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の塔での検出の入力。 -/
lemma representableHomotopyLimitComparison_tower_homotopyEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x))
    [KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) :=
  bousfieldKanConeComparison_tower_homotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x) hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
