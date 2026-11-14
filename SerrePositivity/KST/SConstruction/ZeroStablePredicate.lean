module
public import SerrePositivity.KST.SConstruction.ClosedPredicateOperations
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangleVanishing

/-! # 零対象の閉じた安定頂点条件
概要：零対象であるという条件は同型と全押し出し・引き戻しに閉じる。
方針：零角を持つ四角形を ZeroTriangle とし、二対象の消滅から残りを消す。
規約：零対象を固定しない。使われ方：切断の左右の支持部分圏。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全零対象の条件は実際の安定な閉性条件。 -/
def zeroStablePredicate (X : StableModel.{u}) : ClosedStablePredicate X where
  predicate := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex
  of_iso hx e := hx.of_vertexIso e
  zero_mem hz := hz
  pushout_mem F hF h00 h10 h01 :=
    (⟨F, h01⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X.carrier).zero_cofiber_of_zero_source_middle hF h00 h10
  pullback_mem F hF h10 h01 h11 :=
    (⟨F, h01⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X.carrier).zero_source_of_fiber_zero_middle_cofiber hF h10 h11

end SerrePositivity.KST.SConstruction
