module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallFiberTriangleFaces
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanConePointwiseTriangles

/-!
概要：fiber 比較に使う元の全 pointed 三角形を各点の native 錐の三角形上へ表示する。
方針：全二単体の射影式と native 錐の元の二単体との等式を合成する。
規約：持ち上げや辺を選び直さない。使われ方：指定 fiber 同型と native 可換性の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)

/-- 元の全 pointed 三角形は、同じ二単体を持つ native 錐の三角形の持ち上げ。 -/
lemma coherentSmallFiberPointedTriangle_native_projection
    {K : SSet.{u + 1}} {d : K ⟶ SpaceInfinity.{u}} (c : JoinCone d)
    (k : K _⦋1⦌) (h : nativeConeTriangle c k = coherentTransformationPointTriangle T (ULift.up b)) :
    coherentSmallFiberPointedTriangle F G J x y T b ≫ pointedSpaceProjection =
      fst (Δ[2] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj
          (vertexFiber (smallLeftUnstraighteningProjection F) b)) ≫
        SSet.yonedaEquiv.symm (nativeConeTriangle c k) := by
  rw [coherentSmallFiberPointedTriangle_projection, h,
    coherentTransformationPointTriangle, Equiv.symm_apply_apply]

variable (X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "a" => Functor.obj SSet.uliftFunctor
  (vertexFiber (smallLeftUnstraighteningProjection F) b)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b

/-- 模型 fiber 比較の左三角形の全持ち上げは元の native 錐の左三角形上にある。 -/
lemma coherentCospanPointedFiberTriangle_left_projection :
    coherentSmallFiberPointedTriangle F X Z C.toLeft C.fromLeft C.leftTriangle b ≫
      pointedSpaceProjection =
    fst (Δ[2] : SSet.{u + 1}) a ≫
      SSet.yonedaEquiv.symm (nativeConeTriangle c (SSet.yonedaEquiv horn₂₂.ι₀₂)) :=
  coherentSmallFiberPointedTriangle_native_projection F X Z C.toLeft C.fromLeft
    C.leftTriangle b c _ (coherentCospanConePointwiseCone_leftTriangle F X Y Z C b)

/-- 模型 fiber 比較の右三角形の全持ち上げは元の native 錐の右三角形上にある。 -/
lemma coherentCospanPointedFiberTriangle_right_projection :
    coherentSmallFiberPointedTriangle F Y Z C.toRight C.fromRight C.rightTriangle b ≫
      pointedSpaceProjection =
    fst (Δ[2] : SSet.{u + 1}) a ≫
      SSet.yonedaEquiv.symm (nativeConeTriangle c (SSet.yonedaEquiv horn₂₂.ι₁₂)) :=
  coherentSmallFiberPointedTriangle_native_projection F Y Z C.toRight C.fromRight
    C.rightTriangle b c _ (coherentCospanConePointwiseCone_rightTriangle F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
