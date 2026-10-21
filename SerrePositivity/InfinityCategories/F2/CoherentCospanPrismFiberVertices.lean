module

public import SerrePositivity.InfinityCategories.F2.CoherentPrismFiberTriangleImage
public import SerrePositivity.InfinityCategories.F2.CoherentCospanPrismFiberFunctor

/-!
概要：同じ共通関手の普遍・左右長辺の実頂点を、元の fiber 射の関手頂点へ揃える。
方針：各三角形の実頂点公式を同じ関手に適用し、native 長辺の頂点等式を写す。
規約：両端の明示した等式を保持。使われ方：native path 像の左右合成との比較。
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
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "q" => coherentCospanNativeLongBase F X Y Z C b
local notation "hq" => coherentCospanNativeLongBase_initial F X Y Z C b
local notation "H" => coherentCospanPrismFiberFunctor F X Y Z C b
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "hl" => Eq.trans (Category.assoc cl cf pZ)
  (Eq.trans (congrArg (fun k => cl ≫ k)
    (coherentTransformationTotalMap_projection X Z C.fromLeft))
    (coherentTransformationTotalMap_projection F X C.toLeft))
local notation "hr" => Eq.trans (Category.assoc cr cg pZ)
  (Eq.trans (congrArg (fun k => cr ≫ k)
    (coherentTransformationTotalMap_projection Y Z C.fromRight))
    (coherentTransformationTotalMap_projection F Y C.toRight))

/-- 左の元の長辺頂点の像は、元の実際の左二射の合成の fiber 射。 -/
lemma coherentCospanPrismFiber_obj_longLeft :
    (H).obj (SSet.HomotopyCategory.mk (coherentCospanRestrictedLongLeft F X Y Z C b)) =
      SSet.HomotopyCategory.mk (functorVertex (vertexFiberMap pF pZ (cl ≫ cf) hl b)) :=
  coherentPrismFiberFunctor_obj_long F X Z C.toLeft C.fromLeft C.leftTriangle b q hq
    (coherentCospanRestrictedPrismBase_left F X Y Z C b)

/-- 右も同じ共通関手で元の実際の二射の合成の fiber 射へ写る。 -/
lemma coherentCospanPrismFiber_obj_longRight :
    (H).obj (SSet.HomotopyCategory.mk (coherentCospanRestrictedLongRight F X Y Z C b)) =
      SSet.HomotopyCategory.mk (functorVertex (vertexFiberMap pF pZ (cr ≫ cg) hr b)) :=
  coherentPrismFiberFunctor_obj_long F Y Z C.toRight C.fromRight C.rightTriangle b q hq
    (coherentCospanRestrictedPrismBase_right F X Y Z C b)

/-- native 全錐側の左長辺も同じ実際の fiber 射へ写る。 -/
lemma coherentCospanPrismFiber_obj_nativeLongLeft :
    (H).obj (SSet.HomotopyCategory.mk (coherentCospanNativeLeftOldLongVertex F X Y Z C b)) =
      SSet.HomotopyCategory.mk (functorVertex (vertexFiberMap pF pZ (cl ≫ cf) hl b)) :=
  (congrArg (fun v => (H).obj (SSet.HomotopyCategory.mk v))
    (coherentCospanRestrictedLongLeft_eq F X Y Z C b).symm).trans
      (coherentCospanPrismFiber_obj_longLeft F X Y Z C b)

/-- native 全錐側の右長辺も同じ実際の fiber 射へ写る。 -/
lemma coherentCospanPrismFiber_obj_nativeLongRight :
    (H).obj (SSet.HomotopyCategory.mk (coherentCospanNativeRightOldLongVertex F X Y Z C b)) =
      SSet.HomotopyCategory.mk (functorVertex (vertexFiberMap pF pZ (cr ≫ cg) hr b)) :=
  (congrArg (fun v => (H).obj (SSet.HomotopyCategory.mk v))
    (coherentCospanRestrictedLongRight_eq F X Y Z C b).symm).trans
      (coherentCospanPrismFiber_obj_longRight F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
