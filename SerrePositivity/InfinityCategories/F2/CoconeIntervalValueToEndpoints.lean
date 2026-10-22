module

public import SerrePositivity.InfinityCategories.F2.PointedFiberValueTo
public import SerrePositivity.InfinityCategories.F2.CoconeIntervalHomUnitVertices

/-!
概要：同じ raw/native 区間族の二実端点を、一つの固定値の中で直接照合する。
方針：指定頂点等式と元の族の一致を消去し、全射の実際の頂点を計算する。
規約：同型の HEq から端点を抽出しない。使われ方：下側輸送因子の厳密な消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B T : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}} (c : JoinCocone F)
  {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z')
  (a : T ⟶ intervalMappingSpace c.vertex z) (a' : T ⟶ intervalMappingSpace c.vertex z')
  (ha : HEq a a') (l : T _⦋0⦌)
include ha

/-- 同じ区間族の合成作用の二表示は、固定値への元の全射として厳密に一致する。 -/
lemma coconeIntervalRelativeComposite_valueTo_vertex_eq :
    (coconeIntervalRelativeComposite c a ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom ≫
        (ihom (leftUnstraightening F)).map (pointedFiberValueTo hz)).app (Opposite.op ⦋0⦌) l =
    (coconeIntervalRelativeComposite c a' ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z').hom ≫
        (ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z').hom).app
          (Opposite.op ⦋0⦌) l := by
  cases hz
  cases eq_of_heq ha
  rfl

/-- 同じ普遍輸送の終点も、元の余錐 fiber 写像と固定値への作用として厳密に一致する。 -/
lemma coconeIntervalTransport_valueTo_vertex_eq :
    ((pointedIntervalTransport a).map ≫
      (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z) ≫
        (ihom (leftUnstraightening F)).map (pointedFiberValueTo hz)).app (Opposite.op ⦋0⦌) l =
    ((pointedIntervalTransport a').map ≫
      (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z') ≫
        (ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z').hom).app
          (Opposite.op ⦋0⦌) l := by
  cases hz
  cases eq_of_heq ha
  rfl

end SerrePositivity.InfinityCategories.F2
