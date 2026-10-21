module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanPrismFiberVertices

/-!
概要：共通関手による左右の直接の指定像を、元の実際の fiber 三角形同型へ同定する。
方針：各三角形の直接像の正規化定理を同じ共通関手へ適用する。
規約：左右で関手を変えず指定値を保持。使われ方：共通 path 像の左右の指定合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "q" => coherentCospanNativeLongBase F X Y Z C b
local notation "hq" => coherentCospanNativeLongBase_initial F X Y Z C b
local notation "H" => coherentCospanPrismFiberFunctor F X Y Z C b

/-- 共通関手による左の直接の指定像は、元の実際の左 fiber 三角形同型。 -/
lemma coherentCospanPrismFiber_leftTriangle_eq :
    isoNormalizeEndpoints ((H).mapIso (coherentCospanRestrictedLeftComparisonIso F X Y Z C b))
      (coherentPrismFiberFunctor_obj_universal F X Z C.toLeft C.fromLeft C.leftTriangle b q hq
        (coherentCospanRestrictedPrismBase_left F X Y Z C b))
      (coherentCospanPrismFiber_obj_longLeft F X Y Z C b) =
    coherentTransformationTriangleFiberIso F X Z C.toLeft C.fromLeft C.leftTriangle b :=
  coherentPrismFiberFunctor_triangleIso_eq_actual F X Z C.toLeft C.fromLeft C.leftTriangle b q hq
    (coherentCospanRestrictedPrismBase_left F X Y Z C b)

/-- 右も同じ共通関手の直接の指定像から元の実際の右 fiber 三角形同型へ等しい。 -/
lemma coherentCospanPrismFiber_rightTriangle_eq :
    isoNormalizeEndpoints ((H).mapIso (coherentCospanRestrictedRightComparisonIso F X Y Z C b))
      (coherentPrismFiberFunctor_obj_universal F Y Z C.toRight C.fromRight C.rightTriangle b q hq
        (coherentCospanRestrictedPrismBase_right F X Y Z C b))
      (coherentCospanPrismFiber_obj_longRight F X Y Z C b) =
    coherentTransformationTriangleFiberIso F Y Z C.toRight C.fromRight C.rightTriangle b :=
  coherentPrismFiberFunctor_triangleIso_eq_actual F Y Z C.toRight C.fromRight C.rightTriangle b q hq
    (coherentCospanRestrictedPrismBase_right F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
