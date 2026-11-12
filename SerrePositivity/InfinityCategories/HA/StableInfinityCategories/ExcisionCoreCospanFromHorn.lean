module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanEdges
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetClosureRetraction

/-!
概要：比較格子の穿孔 core と元の cospan の実極限を比較する。
方針：固定した初期収縮と標準ホーンの全単体同型を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionCoreCospanFromHorn : (horn 2 2 : SSet.{u}) ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanIndex.{u} :=
  horn₂₂.isPushout.desc _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFirstEdge _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanSecondEdge
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanEdges_target

lemma excisionCoreCospanFromHorn_first : horn₂₂.ι₀₂ ≫ excisionCoreCospanFromHorn.{u} =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFirstEdge := horn₂₂.isPushout.inl_desc _ _ _

lemma excisionCoreCospanFromHorn_second : horn₂₂.ι₁₂ ≫ excisionCoreCospanFromHorn.{u} =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanSecondEdge := horn₂₂.isPushout.inr_desc _ _ _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
