module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointEvaluationFunctor
public import SerrePositivity.InfinityCategories.HomotopyLimits.YonedaRepresentableEdgeEvaluation

/-!
概要：元の Yoneda 脚の恒等点像の比較を、任意の標的への全変換の評価へ送る。
方針：点同型を一つの転置評価関手で写し、同じ元の全 fiber Hom 作用で前合成する。
規約：標的前層は任意。点ごとの比較を自然な族と仮定しない。
使われ方：P_Σ 内の有限余積保存の、各脚への全パラメータ評価比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

variable {C : SSet.{u}} [Quasicategory C] (f : (Δ[1] : SSet.{u}) ⟶ C)
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
local notation "x₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
local notation "y₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)
local notation "b₀" => ULift.up (SSet.opObjEquiv.symm x₀)
local notation "r₀" => representablePresheafInfinity y₀
local notation "v₀" => NatTrans.app
  (canonicalYonedaTransformationFiberEvaluation x₀ r₀) (Opposite.op ⦋0⦌)
    (intervalMappingVertexOfEdge (yonedaRepresentableNativeEdge f))

/-- 同じ恒等点像と反変輸送点の比較は、任意の標的への全変換の評価と両立する。 -/
def yonedaRepresentableNativeEdge_evaluationActionIso :
    FunctorIso
      (leftUnstraighteningMappingFiberHom r₀ F b₀ ≫ evaluateFunctorAt v₀)
      (leftUnstraighteningMappingFiberHom r₀ F b₀ ≫
        evaluateFunctorAt (yonedaIdentityNormalizedTargetPoint f)) :=
  (evaluateFunctorAt_vertexIso
    (X := vertexFiber pointedSpaceProjection (NatTrans.app r₀ (Opposite.op ⦋0⦌) b₀))
    (Y := vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b₀))
    (yonedaRepresentableNativeEdge_evaluationIso f)).precomp
      (leftUnstraighteningMappingFiberHom r₀ F b₀)

end SerrePositivity.InfinityCategories.HomotopyLimits
