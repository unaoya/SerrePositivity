module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeRestrictionTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.EmptyCone

/-!
概要：任意の空形状上の元の錐の極限性は、元の頂点の終対象性と同値。
方針：空部分複体との同型に沿い、slice の頂点射影の厳密な同型を回収する。
規約：元の形状・図式・錐を変更しない。使われ方：filtered 極限交換の空形状の場合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 任意の空形状上の slice の頂点射影は厳密な同型。 -/
lemma emptyShapeSliceProjection_isIso {K X : SSet.{u}} (hK : ¬ K.Nonempty) (p : K ⟶ X) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) := by
  let e : K ≅ (⊥ : X.Subcomplex) :=
    (SSet.isInitialOfNotNonempty hK).uniqueUpToIso Subcomplex.isInitialBot
  have hi : e.inv ≫ p = (⊥ : X.Subcomplex).ι := Subcomplex.isInitialBot.hom_ext _ _
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p e.inv) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_isIso p e.inv
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedConeRestriction p e.inv hi) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedConeRestriction]
    infer_instance
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedConeRestriction_projection p e.inv hi]
  infer_instance

/-- 任意の空形状上の元の錐が極限であることと、その頂点の終対象性は同値。 -/
lemma isLimitCone_emptyShape_iff_vertex {K X : SSet.{u}} (hK : ¬ K.Nonempty)
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex c.vertex := by
  have := emptyShapeSliceProjection_isIso hK p
  constructor
  · intro hc
    exact hc.map_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)
  · intro hc
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) hc

end SerrePositivity.InfinityCategories.Project.FilteredExchange
