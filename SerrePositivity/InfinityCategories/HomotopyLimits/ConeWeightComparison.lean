module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeWeight
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanLimits
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus

/-!
概要：補助重みの比較射と Bousfield–Kan の標準比較射の厳密な整合性。
方針：重みの制限との可換性と、定値一点重みの終対象性を使う。
規約：元の重み側の制限の同値性はまだ仮定にも結論にも含めない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の標準比較の分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {I : Type u} [SmallCategory I]

/-- 概要：補助重みへの錐の比較射を元の重みに制限すると標準比較射。
方針：重みの制限と weightedConeComparison の可換性を使う。
規約：錐の極限性は不要。
使われ方：Kerodon 7.5.3.12 の κ の二段の表示。 -/
lemma bousfieldKanConeComparison_factorization {H : I ⥤ SSet.{u}} (c : Cone H) :
    weightedConeComparison (bousfieldKanConeWeight I) c ≫
        weightedSectionsPre bousfieldKanConeWeightInclusion H =
      bousfieldKanConeComparison c :=
  weightedConeComparison_pre bousfieldKanConeWeightInclusion c

/-- 概要：補助重みへの錐の比較射を新しい始対象で制限すると一点重みの比較射。
方針：重みの制限と錐の比較射の一般公式を使う。
規約：元の over 圏の恒等射の頂点での評価とは区別する。
使われ方：Kerodon 7.5.3.12 の一点側の可換三角形。 -/
lemma bousfieldKanConeWeightComparison_point {H : I ⥤ SSet.{u}} (c : Cone H) :
    weightedConeComparison (bousfieldKanConeWeight I) c ≫
        weightedSectionsPre bousfieldKanConeWeightPoint H =
      weightedConeComparison ((Functor.const I).obj (Δ[0] : SSet.{u})) c :=
  weightedConeComparison_pre bousfieldKanConeWeightPoint c

/-- 概要：fibration の塔の strict な極限錐から補助重みの end への比較射はホモトピー同値。
方針：一点側の制限は trivial Kan fibration で、合成は終対象重みの比較同型になる。
規約：零段の Kan 性、隣接遷移の Fibration 性、通常の単体集合での極限性を前提とする。
使われ方：Kerodon 7.5.3.12 の κ の分解の最初の射。 -/
lemma bousfieldKanConeWeightComparison_tower_homotopyEquivalence
    {H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (c : Cone H) (hc : IsLimit c)
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsSimplicialHomotopyEquivalence
      (weightedConeComparison (bousfieldKanConeWeight (AsSmall.{u} ℕᵒᵖ)) c) := by
  let U := (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj (Δ[0] : SSet.{u})
  have hU : IsTerminal U := weightIsTerminalOfObj U (fun _ => stdSimplex.isTerminalObj₀)
  have := weightedConeComparison_isIso_of_isTerminalWeight U hU c hc
  have := weightedSections_tower_kanComplex U H
  have := kanComplex_of_iso (asIso (weightedConeComparison U c)).symm
  have := weightedSections_tower_kanComplex
    (bousfieldKanConeWeight (AsSmall.{u} ℕᵒᵖ)) H
  apply (weightedSectionsPre_tower_homotopyEquivalence (H := H)
    bousfieldKanConeWeightPoint bousfieldKanConeWeightPoint_anodyne).cancel_right
  rw [bousfieldKanConeWeightComparison_point]
  exact homotopyEquivalence_of_isIso (weightedConeComparison U c)

end SerrePositivity.InfinityCategories.HomotopyLimits
