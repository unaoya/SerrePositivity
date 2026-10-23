module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeFiberEdgeSections

/-!
概要：元の native 切断の左右の指定比較を、実際の fiber 二脚と切断比較同値へ結ぶ。
方針：局所全三角形の同じ図式面の切断族を、実際の第一 fiber 射と第二作用の切断へ同定する。
規約：元の全三角形の指定比較を保持。使われ方：元の模型 fiber 比較への普遍性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "Dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "Dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "fl" => vertexFiberMap pF pX (coherentTransformationTotalMap F X C.toLeft)
  (coherentTransformationTotalMap_projection F X C.toLeft) b
local notation "fr" => vertexFiberMap pF pY (coherentTransformationTotalMap F Y C.toRight)
  (coherentTransformationTotalMap_projection F Y C.toRight) b

/-- 左の元の指定比較は、元の実際の左 fiber 射と標的側の切断比較同値へ接続する。 -/
def coherentCospanNativeLeftFiberSectionsIso :
    FunctorIso (coherentCospanNativeSectionPullback F X Y Z C b ≫ pullback.fst f g)
      ((SSet.uliftFunctor.{u + 1, u}).map fl ≫
        coherentCospanNativeLeftFiberEdgeSections F X Y Z C b) :=
  functorIsoOfEq (coherentCospanNativeLeftDiagramSectionsIso F X Y Z C b) rfl (by
    have hj : stdSimplex.δ (0 : Fin 3) ≫ Dl = horn₂₂.ι₀₂ ≫ d := by
      simpa only [Equiv.symm_apply_apply, coherentCospanConePointwiseCone] using
        nativeConeTriangle_diagram_edge c el
    exact coherentSmallFiberTriangleDiagramSections_eq F X Z C.toLeft C.fromLeft
      C.leftTriangle b Dl (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C)
      (horn₂₂.ι₀₂ ≫ d) (coherentCospanNativeLeftDiagramEdge_eq_point F X Y Z C b) hj)

/-- 右の元の指定比較も、同じ元の右 fiber 射と標的側の切断比較同値へ接続する。 -/
def coherentCospanNativeRightFiberSectionsIso :
    FunctorIso (coherentCospanNativeSectionPullback F X Y Z C b ≫ pullback.snd f g)
      ((SSet.uliftFunctor.{u + 1, u}).map fr ≫
        coherentCospanNativeRightFiberEdgeSections F X Y Z C b) :=
  functorIsoOfEq (coherentCospanNativeRightDiagramSectionsIso F X Y Z C b) rfl (by
    have hj : stdSimplex.δ (0 : Fin 3) ≫ Dr = horn₂₂.ι₁₂ ≫ d := by
      simpa only [Equiv.symm_apply_apply, coherentCospanConePointwiseCone] using
        nativeConeTriangle_diagram_edge c er
    exact coherentSmallFiberTriangleDiagramSections_eq F Y Z C.toRight C.fromRight
      C.rightTriangle b Dr (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C)
      (horn₂₂.ι₁₂ ≫ d) (coherentCospanNativeRightDiagramEdge_eq_point F X Y Z C b) hj)

end SerrePositivity.InfinityCategories.F2
