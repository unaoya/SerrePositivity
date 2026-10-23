module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanPrismTriangleImages
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IsoMappedSpanNormalization
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanFiberPathComposition

/-!
概要：native 全錐の指定 path の fiber 像を、元の左右三角形の指定 fiber 同型の合成へ同定する。
方針：同じ共通関手の指定像を両端で補正し、中間の補正を明示的に相殺する。
規約：元の実全錐と指定同型の値を保持。使われ方：native 普遍性による模型 fiber 比較の判定。
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

/-- native 指定長辺の像を、元の実際の合成 fiber 射を両端とする同型へ揃える。 -/
def coherentCospanNativeFiberPathIso :=
  isoNormalizeEndpoints (coherentCospanNativePrismFiberPathIso F X Y Z C b)
    (coherentCospanPrismFiber_obj_nativeLongLeft F X Y Z C b)
    (coherentCospanPrismFiber_obj_nativeLongRight F X Y Z C b)

/-- 元の native 全錐の指定像は元の左右の実際の fiber 三角形同型の指定合成に等しい。 -/
lemma coherentCospanNativeFiberPathIso_eq_triangles :
    coherentCospanNativeFiberPathIso F X Y Z C b =
      coherentCospanConeFiberTrianglePathIso F X Y Z C b := by
  let hmid := congrArg SSet.HomotopyCategory.mk (congrArg functorVertex
    (congrArg (fun t => vertexFiberMap pF pZ (coherentTransformationTotalMap F Z t)
      (coherentTransformationTotalMap_projection F Z t) b) C.diagonal_eq))
  have hs := functor_mapIso_normalized_span H
    (coherentCospanRestrictedLeftComparisonIso F X Y Z C b)
    (coherentCospanRestrictedRightComparisonIso F X Y Z C b)
    (congrArg SSet.HomotopyCategory.mk (coherentCospanRestrictedUniversal_eq F X Y Z C b))
    (congrArg SSet.HomotopyCategory.mk (coherentCospanRestrictedLongLeft_eq F X Y Z C b))
    (congrArg SSet.HomotopyCategory.mk (coherentCospanRestrictedLongRight_eq F X Y Z C b))
    (coherentPrismFiberFunctor_obj_universal F X Z C.toLeft C.fromLeft C.leftTriangle b q hq
      (coherentCospanRestrictedPrismBase_left F X Y Z C b))
    (coherentPrismFiberFunctor_obj_universal F Y Z C.toRight C.fromRight C.rightTriangle b q hq
      (coherentCospanRestrictedPrismBase_right F X Y Z C b))
    (coherentCospanPrismFiber_obj_nativeLongLeft F X Y Z C b)
    (coherentCospanPrismFiber_obj_nativeLongRight F X Y Z C b) hmid
  rw [coherentCospanPrismFiber_leftTriangle_eq,
    coherentCospanPrismFiber_rightTriangle_eq] at hs
  unfold coherentCospanNativeFiberPathIso
  rw [← coherentCospanRestrictedPrismFiberPathIso_eq_native]
  unfold coherentCospanConeFiberTrianglePathIso
  rw [functorEqIso_eqToIso]
  simpa only [isoNormalizeEndpoints, coherentCospanRestrictedPrismFiberPathIso,
    coherentCospanRestrictedPrismPathIso, Iso.trans_assoc] using hs

local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "fb" => vertexFiberMap (cf ≫ pZ) pZ cf rfl b
local notation "gb" => vertexFiberMap (cg ≫ pZ) pZ cg rfl b
local notation "m" => coherentCospanConeTotalModelFiberComparison F X Y Z C b
local instance : KanComplex (vertexFiber pZ b) := vertexFiber_kanComplex_of_leftFibration pZ b

/-- 実際の模型 fiber 比較の指定可換同型は、元の native 全錐の同じ指定像。 -/
lemma coherentCospanModelFiberPathIso_eq_native :
    functorIsoOfEq ((intervalPullbackPathIso fb gb).precomp m)
      (coherentCospanConeFiberComparisonPath_left F X Y Z C b)
      (coherentCospanConeFiberComparisonPath_right F X Y Z C b) =
    coherentCospanNativeFiberPathIso F X Y Z C b :=
  (coherentCospanConeFiberComparisonPathIso_eq_triangles F X Y Z C b).trans
    (coherentCospanNativeFiberPathIso_eq_triangles F X Y Z C b).symm

end SerrePositivity.InfinityCategories.F2
