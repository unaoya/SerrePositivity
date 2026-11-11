module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanModelTotalEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FiberwisePullbackKanWeakEquivalence

/-!
概要：各点の native 極限性から元の全空間 Kan 引き戻し比較の同値性を証明する。
方針：元の全空間比較を Kan 置換し、filtered な底の引き戻し比較と合成する。
規約：元の全空間射と三座標を保持。使われ方：native 比較候補への同値性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "p" => smallLeftUnstraighteningProjection Z
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local instance : LeftFibration (cf ≫ p) := by
  rw [coherentTransformationTotalMap_projection]
  infer_instance
local instance : LeftFibration (cg ≫ p) := by
  rw [coherentTransformationTotalMap_projection]
  infer_instance

/-- 元の底上の模型比較を Kan 置換し、同じ元の Kan cospan の引き戻しへ送る。 -/
def coherentCospanConeKanComparison :
    continuousKanReplacement.obj (smallLeftUnstraightening F) ⟶
      intervalPullback (continuousKanReplacement.map cf) (continuousKanReplacement.map cg) :=
  continuousKanReplacement.map (coherentCospanConeTotalModelComparison F X Y Z C) ≫
    fiberwisePullbackKanComparison p cf cg

/-- 各点の元の錐が極限なら、filtered な底上の元の Kan 比較は弱同値。 -/
lemma coherentCospanConeKanComparison_isWeakHomotopyEquivalence
    [Quasicategory B] [IsFilteredInfinity B]
    (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b)) :
    IsWeakHomotopyEquivalence (coherentCospanConeKanComparison F X Y Z C) :=
  (continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (coherentCospanConeTotalModelComparison_isWeakHomotopyEquivalence F X Y Z C hc)).comp
      (fiberwisePullbackKanComparison_isWeakHomotopyEquivalence p cf cg)

/-- 同じ元の Kan 比較には実際の単体的ホモトピー逆が存在する。 -/
lemma coherentCospanConeKanComparison_homotopyEquivalence
    [Quasicategory B] [IsFilteredInfinity B]
    (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b)) :
    IsSimplicialHomotopyEquivalence (coherentCospanConeKanComparison F X Y Z C) := by
  have h := coherentCospanConeKanComparison_isWeakHomotopyEquivalence F X Y Z C hc
  exact h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
