module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeFiberEvaluation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCoconeTotalComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeTransformationPoint

/-!
概要：指定頂点へ表示を移した余錐の fiber 写像を、元の値への全空間写像として追跡する。
方針：頂点の等式と既存の fiber の値の比較を続け、標準比較の頂点と同定する。
規約：元の余錐と頂点の等式を保持する。
使われ方：全空間余錐の単位比較を実際の写像の比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の fiber 写像を指定頂点の元の値への写像として表示する。
方針：頂点の等式による移送と元の値の比較を合成する。
規約：元の fiber 写像を用いる。使われ方：単位との全空間写像としての比較。 -/
def coconeFiberValueMapAt {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
    (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) (hv : c.vertex = z) :
    leftUnstraightening F ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj :=
  coconeFiberMap c ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection) hv) ≫
    (pointedSpaceFiberValueEquivalence z).hom

/-- 概要：元の値への全空間写像の頂点は元の定値標的比較の像そのもの。
方針：頂点の等式を消去し、fiber 写像の元の比較頂点を後合成する。
規約：元の余錐の点を保持。使われ方：小さい内部 Hom の単位比較との接続。 -/
lemma coconeFiberValueMapAt_vertex {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
    (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) (hv : c.vertex = z) :
    functorVertex (coconeFiberValueMapAt c z hv) =
      (coherentConstantTargetMap F z).app (Opposite.op ⦋0⦌)
        ((coconeTransformationMap F z).app (Opposite.op ⦋0⦌) (coconeMappingPointAt c z hv)) := by
  cases hv
  simp only [coconeFiberValueMapAt, eqToHom_refl, Category.id_comp]
  change ((ihom (leftUnstraightening F)).map
    (pointedSpaceFiberValueEquivalence c.vertex).hom).app (Opposite.op ⦋0⦌)
      (functorVertex (coconeFiberMap c)) = _
  exact congrArg (fun v ↦ ((ihom (leftUnstraightening F)).map
    (pointedSpaceFiberValueEquivalence c.vertex).hom).app (Opposite.op ⦋0⦌) v)
      (coconeFiberMap_vertex c)

/-- 概要：小さい全空間比較の元の余錐の点を戻すと、実際の元の値への写像の頂点。
方針：内部 Hom の縮小同型の往復を消去する。
規約：指定頂点の等式も保持。使われ方：単位比較の大きい全空間への移送。 -/
lemma coconeFiberValueMapAt_smallComparison {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) (hv : c.vertex = z) :
    (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv.app (Opposite.op ⦋0⦌)
      ((coherentCoconeTotalComparison F z).app (Opposite.op ⦋0⦌)
        (coconeMappingPointAt c z hv)) = functorVertex (coconeFiberValueMapAt c z hv) := by
  have h : coherentCoconeTotalComparison F z ≫
      (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv =
        coconeTransformationMap F z ≫ coherentConstantTargetMap F z := by
    simp only [coherentCoconeTotalComparison, coherentSmallConstantTargetMap,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) (coconeMappingPointAt c z hv)) h
  exact e.trans (coconeFiberValueMapAt_vertex c z hv).symm

end SerrePositivity.InfinityCategories.F2
