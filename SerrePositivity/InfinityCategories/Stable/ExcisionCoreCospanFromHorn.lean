module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanEdges
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LimitConeExtension
public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Core.LeftPrism
public import SerrePositivity.InfinityCategories.Core.PrismFilling
public import SerrePositivity.InfinityCategories.Stable.PosetClosureRetraction

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
namespace SerrePositivity.InfinityCategories

def excisionCoreCospanFromHorn : (horn 2 2 : SSet.{u}) ⟶
    nerve ExcisionCoreCospanIndex.{u} :=
  horn₂₂.isPushout.desc excisionCoreCospanFirstEdge excisionCoreCospanSecondEdge
    excisionCoreCospanEdges_target

lemma excisionCoreCospanFromHorn_first : horn₂₂.ι₀₂ ≫ excisionCoreCospanFromHorn.{u} =
    excisionCoreCospanFirstEdge := horn₂₂.isPushout.inl_desc _ _ _

lemma excisionCoreCospanFromHorn_second : horn₂₂.ι₁₂ ≫ excisionCoreCospanFromHorn.{u} =
    excisionCoreCospanSecondEdge := horn₂₂.isPushout.inr_desc _ _ _

end SerrePositivity.InfinityCategories
