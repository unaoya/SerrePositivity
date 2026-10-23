module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentFiberImage
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentFiberPathIsoEquality

/-!
概要：元の模型 fiber 比較の可換同型を元の左右三角形の fiber 同型の合成で表示する。
方針：指定相対像の合成・反転・共通長辺の等式の保存を適用する。
規約：元の二三角形と指定値を保持。使われ方：各点の native 錐の可換性との照合。
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
local notation "p" => smallLeftUnstraighteningProjection Z
local notation "a" => smallLeftUnstraighteningProjection F
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "fb" => vertexFiberMap (cf ≫ p) p cf rfl b
local notation "gb" => vertexFiberMap (cg ≫ p) p cg rfl b
local notation "m" => coherentCospanConeTotalModelFiberComparison F X Y Z C b
local instance : KanComplex (vertexFiber p b) := vertexFiber_kanComplex_of_leftFibration p b

/-- 元の二つの fiber 三角形比較を同じ共通長辺を介して合成した指定可換同型。 -/
def coherentCospanConeFiberTrianglePathIso :=
  (coherentTransformationTriangleFiberIso F X Z C.toLeft C.fromLeft C.leftTriangle b).symm ≪≫
    functorEqIso (congrArg (fun t => vertexFiberMap a p (coherentTransformationTotalMap F Z t)
      (coherentTransformationTotalMap_projection F Z t) b) C.diagonal_eq) ≪≫
    coherentTransformationTriangleFiberIso F Y Z C.toRight C.fromRight C.rightTriangle b

/-- 元の相対可換同型の指定 fiber 像は元の左右 fiber 三角形比較の合成。 -/
lemma coherentCospanConeRelativePathIso_fiber_image :
    relativeIsoFiberImage p a
      (by rw [Category.assoc, coherentTransformationTotalMap_projection,
        coherentTransformationTotalMap_projection])
      (by rw [Category.assoc, coherentTransformationTotalMap_projection,
        coherentTransformationTotalMap_projection])
      (coherentCospanConeRelativePathIso F X Y Z C) b =
        coherentCospanConeFiberTrianglePathIso F X Y Z C b := by
  unfold coherentCospanConeRelativePathIso
  rw [relativeIsoFiberImage_trans, relativeIsoFiberImage_trans, relativeIsoFiberImage_symm,
    coherentTransformationRelativeEq_fiberImage F Z b C.diagonal_eq]
  rw [← coherentTransformationTriangleFiberIso_eq_image,
    ← coherentTransformationTriangleFiberIso_eq_image]
  rfl

/-- 実際の模型 fiber 比較の指定 path 同型は元の左右三角形の同じ fiber 同型の合成。 -/
lemma coherentCospanConeFiberComparisonPathIso_eq_triangles :
    functorIsoOfEq ((intervalPullbackPathIso fb gb).precomp m)
      (coherentCospanConeFiberComparisonPath_left F X Y Z C b)
      (coherentCospanConeFiberComparisonPath_right F X Y Z C b) =
    coherentCospanConeFiberTrianglePathIso F X Y Z C b :=
  (coherentCospanConeFiberComparisonPathIso_eq F X Y Z C b).trans
    (coherentCospanConeRelativePathIso_fiber_image F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
