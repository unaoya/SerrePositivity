module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantTargetValueProjectionTo
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeIntervalHomEndpointTransport

/-!
概要：元の pointed fiber の値射を、指定した頂点等式の先の固定値へ移す。
方針：同じ等式による標的表示の変更を、全射影と区間 Hom の成分に適用する。
規約：指定等式・元の成分を保持。使われ方：下側輸送と定値三角形の同じ値での消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の pointed fiber から、指定した頂点等式の先の固定値への射。 -/
def pointedFiberValueTo {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    vertexFiber pointedSpaceProjection z ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z').obj := by
  subst z'
  exact (pointedSpaceFiberValueEquivalence z).hom

/-- 同じ固定値への全射影は、元の定値相対比較と同じ fiber の値射の合成。 -/
lemma constantTargetValueProjectionTo_eq_fiberValueTo {B C : SSet.{u + 1}} (p : C ⟶ B)
    {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    constantTargetValueProjectionTo p hz =
      (constantUnstraighteningRelativeIso p z).hom ≫ (ihom C).map (pointedFiberValueTo hz) := by
  cases hz
  rfl

/-- 終点表示だけを移した同じ Hom 成分は、一つの固定値への像としても一致する。 -/
lemma coconeIntervalFiberHomIso_app_valueTo_heq_of_target_eq {B T : SSet.{u + 1}}
    [Quasicategory T] {F : B ⟶ SpaceInfinity.{u}} (c : JoinCocone F)
    {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z')
    (a : T ⟶ intervalMappingSpace c.vertex z) (a' : T ⟶ intervalMappingSpace c.vertex z')
    (ha : HEq a a') (l : T _⦋0⦌) :
    HEq (VertexIso.map ((coconeIntervalFiberHomIso c a).app l)
      ((ihom (leftUnstraightening F)).map (pointedFiberValueTo hz)))
      (VertexIso.map ((coconeIntervalFiberHomIso c a').app l)
        ((ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z').hom)) := by
  cases hz
  cases eq_of_heq ha
  rfl

end SerrePositivity.InfinityCategories.F2
