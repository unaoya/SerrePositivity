module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeWeightPointCorner

/-!
概要：一脚が fibration の cospan の補助重みへの比較と一点側の制限の同値性。
方針：補助重みの右脚の単射性で end を Kan にし、実際に証明した一点側の相対境界を使う。
規約：元の Bousfield–Kan 重みへの制限と κ 全体の同値性は後続の別の証明が必要。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の一脚の fibration 性での標準比較の第一段階。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]

/-- 概要：中央と右端が Kan、左脚が fibration の cospan の補助重みの end は Kan。
方針：補助重みの右脚の単射性を添字の単射から得て、一脚のホーン充填を使う。
規約：図式の右脚の fibration 性は要求しない。
使われ方：Kerodon 7.5.3.12 の補助重みの切断空間。 -/
lemma bousfieldKanConeWeight_cospan_leftFibration_kanComplex :
    KanComplex (weightedSections (bousfieldKanConeWeight (AsSmall.{u} WalkingCospan)) H) := by
  have : (AsSmall.up : WalkingCospan ⥤ AsSmall.{u} WalkingCospan).IsEquivalence :=
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).isEquivalence_functor
  have := bousfieldKanConeWeight_map_mono (AsSmall.up.map WalkingCospan.Hom.inr)
  exact weightedSections_cospan_leftFibration_kanComplex _ H

/-- 概要：補助重みの end から一点重みの end への実際の制限は一脚の fibration 性で trivial Kan fibration。
方針：一点包含の成分ごとの anodyne 性と実際に検証した中央の相対境界を使う。
規約：未証明の重みの境界条件を前提に追加しない。
使われ方：Kerodon 7.5.3.12 の strict 極限側の比較の同値性。 -/
lemma bousfieldKanConeWeightPoint_cospan_leftFibration_trivialKanFibration :
    TrivialKanFibration (weightedSectionsPre bousfieldKanConeWeightPoint H) :=
  weightedSectionsPre_cospan_leftFibration_trivialKanFibration
    bousfieldKanConeWeightPoint bousfieldKanConeWeightPoint_anodyne
    bousfieldKanConeWeightPoint_cospan_corner_anodyne

/-- 概要：一脚が fibration の cospan の strict 極限から補助重みの end への比較はホモトピー同値。
方針：一点側の制限は trivial Kan fibration、合成は終対象重みの比較同型であることを使う。
規約：中央と右端の Kan 性、左脚の Fibration 性と極限性を前提とし、頂点の Kan 性は導出する。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の κ の分解の第一の射。 -/
lemma bousfieldKanConeWeightComparison_cospan_leftFibration_homotopyEquivalence
    (c : Cone H) (hc : IsLimit c) :
    IsSimplicialHomotopyEquivalence
      (weightedConeComparison (bousfieldKanConeWeight (AsSmall.{u} WalkingCospan)) c) := by
  let U := (Functor.const (AsSmall.{u} WalkingCospan)).obj (Δ[0] : SSet.{u})
  have hU : IsTerminal U := weightIsTerminalOfObj U (fun _ => stdSimplex.isTerminalObj₀)
  have := weightedConeComparison_isIso_of_isTerminalWeight U hU c hc
  have : Mono (U.map (AsSmall.up.map WalkingCospan.Hom.inr)) :=
    inferInstanceAs (Mono (𝟙 (Δ[0] : SSet.{u})))
  have := weightedSections_cospan_leftFibration_kanComplex U H
  have := kanComplex_of_iso (asIso (weightedConeComparison U c)).symm
  have := bousfieldKanConeWeight_cospan_leftFibration_kanComplex H
  have := bousfieldKanConeWeightPoint_cospan_leftFibration_trivialKanFibration H
  have hpoint := (isQCatEquivalence_of_trivialKanFibration
    (weightedSectionsPre bousfieldKanConeWeightPoint H)).isSimplicialHomotopyEquivalence
  apply hpoint.cancel_right
  rw [bousfieldKanConeWeightComparison_point]
  exact homotopyEquivalence_of_isIso (weightedConeComparison U c)

end SerrePositivity.InfinityCategories.HomotopyLimits
