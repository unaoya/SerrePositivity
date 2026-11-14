module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEdgeCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits

/-!
概要：同じjoin錐の後合成は、指定脚の実際の一次単体をそのまま写す。
方針：join脚のYoneda表示と後合成の自然性を使う。
規約：IS-W2 C04の既存構成の合成・評価則。頂点と図式の脚を固定する。
使われ方：Kerodon 7.1、HA 1.2.4、指定Tot錐の導来圏への輸送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial

/-- 元の錐の後合成と、同じ指定脚の一次単体の像は厳密に一致する。 -/
theorem derivedConeLeg_mapJoinCone {K X Y : SSet.{u}} {p : K ⟶ X}
    (f : X ⟶ Y) (c : JoinCone p) (v : K _⦋0⦌) :
    (derivedConeLeg (mapJoinCone f c) v).edge =
      f.app (Opposite.op ⦋1⦌) (derivedConeLeg c v).edge := by
  change SSet.yonedaEquiv (_ ≫ _ ≫ (c.val ≫ f)) = _
  rw [← Category.assoc, ← Category.assoc, SSet.yonedaEquiv_comp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
