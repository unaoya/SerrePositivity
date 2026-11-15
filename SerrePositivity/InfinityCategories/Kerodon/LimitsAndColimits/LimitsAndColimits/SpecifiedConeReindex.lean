module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction

/-!
概要：同じ指定錐を添字同型と底図式の等式で移し、その極限性を保つ。
方針：既存slice制限の同型と終頂点の同型不変性、等式消去。
規約：IS-W2 C06・C07の既存構成の合成・移送則。
使われ方：HA 1.2.4、元の全join射を保持する指定Tot錐。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial

/-- 添字同型による同じ指定錐の制限は極限性を保つ。 -/
theorem restrictJoinCone_isLimit_of_isIso {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (f : L ⟶ K) [IsIso f] (hc : IsLimitCone c) :
    IsLimitCone (restrictJoinCone c f) := by
  haveI := sliceOverRestrict_isIso p f
  exact hc.map_of_isIso (sliceOverRestrict p f)

/-- 底図式の等式による指定錐の移送。 -/
def joinConeOfDiagramEq {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCone p) : JoinCone q := h ▸ c

/-- 同じ全join射を保つ。 -/
theorem joinConeOfDiagramEq_val {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCone p) : (joinConeOfDiagramEq h c).val = c.val := by
  subst q
  rfl

/-- 同じ指定錐の極限性を保つ。 -/
theorem joinConeOfDiagramEq_isLimit {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (joinConeOfDiagramEq h c) := by
  subst q
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
