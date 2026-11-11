module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeWeight
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.DiscreteComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus

/-!
概要：補助重みの比較射と Bousfield–Kan の標準比較射の厳密な整合性。
方針：重みの制限との可換性と、定値一点重みの終対象性を使う。
規約：元の重み側の制限の同値性はまだ仮定にも結論にも含めない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の標準比較の分解。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I]

/-- 概要：補助重みへの錐の比較射を元の重みに制限すると標準比較射。
方針：重みの制限と weightedConeComparison の可換性を使う。
規約：錐の極限性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の κ の二段の表示。 -/
lemma bousfieldKanConeComparison_factorization {H : I ⥤ SSet.{u}} (c : Cone H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeight I) c ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightInclusion c

/-- 概要：補助重みへの錐の比較射を新しい始対象で制限すると一点重みの比較射。
方針：重みの制限と錐の比較射の一般公式を使う。
規約：元の over 圏の恒等射の頂点での評価とは区別する。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の一点側の可換三角形。 -/
lemma bousfieldKanConeWeightComparison_point {H : I ⥤ SSet.{u}} (c : Cone H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeight I) c ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightPoint H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison ((Functor.const I).obj (Δ[0] : SSet.{u})) c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightPoint c

/-- 概要：fibration の塔の strict な極限錐から補助重みの end への比較射はホモトピー同値。
方針：一点側の制限は trivial Kan fibration で、合成は終対象重みの比較同型になる。
規約：零段の Kan 性、隣接遷移の Fibration 性、通常の単体集合での極限性を前提とする。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の κ の分解の最初の射。 -/
lemma bousfieldKanConeWeightComparison_tower_homotopyEquivalence
    {H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (c : Cone H) (hc : IsLimit c)
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeight (AsSmall.{u} ℕᵒᵖ)) c) := by
  let U := (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj (Δ[0] : SSet.{u})
  have hU : IsTerminal U := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightIsTerminalOfObj U (fun _ => stdSimplex.isTerminalObj₀)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_isIso_of_isTerminalWeight U hU c hc
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex U H
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison U c)).symm
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeight (AsSmall.{u} ℕᵒᵖ)) H
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_tower_homotopyEquivalence (H := H)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightPoint _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeWeightPoint_anodyne).cancel_right
  rw [bousfieldKanConeWeightComparison_point]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison U c)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
