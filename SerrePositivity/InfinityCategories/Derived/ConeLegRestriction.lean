module
public import SerrePositivity.InfinityCategories.F2.NativeConeLeg
public import SerrePositivity.InfinityCategories.F2.LimitConeExtension
public import SerrePositivity.InfinityCategories.Derived.RoofTargetFunctor
/-!
概要：実錐の形状制限は、同じ頂点での同じ実脚を厳密に保つ。
方針：二点 join の包含と Yoneda の前後合成を計算する。
規約：形状の充填性を仮定しない。使われ方：実分母への cofinal 制限後の脚の可逆性の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
/-- 錐の脚の包含は、元の形状の射に自然。 -/
lemma coneLegInclusion_naturality {L K : SSet.{u}} (u : L ⟶ K) (i : L _⦋0⦌) :
    F2.coneLegInclusion i ≫ joinMap (𝟙 (Δ[0] : SSet.{u})) u =
      F2.coneLegInclusion (u.app (Opposite.op ⦋0⦌) i) := by
  rw [F2.coneLegInclusion, F2.coneLegInclusion, Category.assoc, ← joinMap_comp,
    Category.id_comp, roofTargetPoint]
/-- 形状を制限した実錐の同じ脚は、元の像の頂点での実脚そのもの。 -/
lemma nativeConeLeg_restrict_edge {L K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (u : L ⟶ K) (i : L _⦋0⦌) :
    (F2.nativeConeLeg (F2.restrictJoinCone c u) i).edge =
      (F2.nativeConeLeg c (u.app (Opposite.op ⦋0⦌) i)).edge := by
  change c.val.app (Opposite.op ⦋1⦌)
    ((joinMap (𝟙 (Δ[0] : SSet.{u})) u).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (F2.coneLegInclusion i))) =
        c.val.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (F2.coneLegInclusion (u.app (Opposite.op ⦋0⦌) i)))
  rw [← SSet.yonedaEquiv_comp, coneLegInclusion_naturality]
end SerrePositivity.InfinityCategories
