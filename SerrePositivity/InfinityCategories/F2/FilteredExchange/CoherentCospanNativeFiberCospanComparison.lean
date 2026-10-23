module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeCommonPointFiber

/-!
概要：元の実際の小さい fiber cospan から、native 切断 cospan への厳密な比較を構成する。
方針：両辺の普遍 prism の終点条件を、同じ共通点の切断の表示同型で読む。
規約：元の二作用と共通標的を保持。使われ方：切断の極限と模型 fiber 比較の同値性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "el" => horn₂₂.ι₀₂ ≫ d
local notation "er" => horn₂₂.ι₁₂ ≫ d
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "E" => coherentCospanNativeCommonPointFiberIso F X Y Z C b
local notation "L" => coherentCospanNativeLeftFiberEdgeSections F X Y Z C b
local notation "R" => coherentCospanNativeRightFiberEdgeSections F X Y Z C b

/-- 左の切断比較は、共通終点で元の実際の左から最後への fiber 射を厳密に保持する。 -/
lemma coherentCospanNativeLeftFiberEdgeSections_target :
    L ≫ f ≫ (E).hom = (SSet.uliftFunctor.{u + 1, u}).map ql := by
  rw [coherentCospanNativeCommonPointFiberIso_left]
  exact coherentSmallFiberEdgeSectionsOfEq_target X Z C.fromLeft b el
    (coherentCospanNativeLeftDiagramEdge_eq_point F X Y Z C b)
    (coherentCospanNativeLeftDiagramTarget_vertex F X Y Z C b)

/-- 右も同じ共通終点で、元の実際の右から最後への fiber 射を厳密に保持する。 -/
lemma coherentCospanNativeRightFiberEdgeSections_target :
    R ≫ g ≫ (E).hom = (SSet.uliftFunctor.{u + 1, u}).map qr := by
  rw [coherentCospanNativeCommonPointFiberIso_right]
  exact coherentSmallFiberEdgeSectionsOfEq_target Y Z C.fromRight b er
    (coherentCospanNativeRightDiagramEdge_eq_point F X Y Z C b)
    (coherentCospanNativeRightDiagramTarget_vertex F X Y Z C b)

/-- 元の実 fiber cospan から切断 cospan への、実際の三成分を持つ厳密な自然変換。 -/
def coherentCospanNativeFiberCospanComparison :
    cospan ((SSet.uliftFunctor.{u + 1, u}).map ql) ((SSet.uliftFunctor.{u + 1, u}).map qr) ⟶
      cospan f g :=
  cospanHomMk (E).inv L R (by
    change (SSet.uliftFunctor.{u + 1, u}).map ql ≫ (E).inv = L ≫ f
    apply (cancel_mono (E).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (coherentCospanNativeLeftFiberEdgeSections_target F X Y Z C b).symm) (by
    change (SSet.uliftFunctor.{u + 1, u}).map qr ≫ (E).inv = R ≫ g
    apply (cancel_mono (E).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (coherentCospanNativeRightFiberEdgeSections_target F X Y Z C b).symm)

end SerrePositivity.InfinityCategories.F2
