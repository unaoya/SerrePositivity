module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UnstraighteningFiberPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.YonedaEdgeEvaluationAction

/-!
概要：元の Yoneda 脚による前合成族と、反変輸送点における全評価を結ぶ。
方針：選択済み前合成の全三角形族の合成則を同じ恒等点で評価する。
規約：元の区間 Hom の全パラメータと、元の Yoneda 辺・恒等点を保持する。
使われ方：有限余積の各脚における Yoneda 評価の第一変数の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の選択済み前合成族を同じ点で評価すると、元の第一変換の値で全族を評価する。 -/
def unstraighteningFiberHom_precompose_evaluateIso {B : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex F) (functorVertex G)) (b : B _⦋0⦌)
    (v : (vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b)) _⦋0⦌) :
    FunctorIso
      (intervalPrecompose (functorVertex J)
          (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        leftUnstraighteningMappingFiberHom F J b ≫ evaluateFunctorAt v)
      (leftUnstraighteningMappingFiberHom G J b ≫ evaluateFunctorAt
        ((evaluateFunctorAt v).app (Opposite.op ⦋0⦌)
          ((leftUnstraighteningMappingFiberHom F G b).app (Opposite.op ⦋0⦌)
            (intervalMappingVertexOfEdge e)))) := by
  have h := (unstraighteningFiberHom_precomposeIso F G J e b).postcomp (evaluateFunctorAt v)
  simp only [Category.assoc, SSet.const_comp, functorComposition_evaluate_const] at h
  exact h

variable {C : SSet.{u}} [Quasicategory C] (f : (Δ[1] : SSet.{u}) ⟶ C)
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
local notation "x₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
local notation "y₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)
local notation "b₀" => ULift.up (SSet.opObjEquiv.symm x₀)
local notation "r₀" => representablePresheafInfinity y₀
local notation "v₀" => NatTrans.app
  (canonicalYonedaTransformationFiberEvaluation x₀ r₀) (Opposite.op ⦋0⦌)
    (intervalMappingVertexOfEdge (yonedaRepresentableNativeEdge f))

/-- 元の Yoneda 脚による前合成族の評価は、同じ反変輸送点での全評価と関手同型。 -/
def canonicalYonedaFiberEvaluation_precomposeIso :
    FunctorIso
      (intervalPrecompose (functorVertex F)
          (SSet.Truncated.HomotopyCategory.homMk (yonedaRepresentableNativeEdge f).toTruncated) ≫
        canonicalYonedaTransformationFiberEvaluation x₀ F)
      (leftUnstraighteningMappingFiberHom r₀ F b₀ ≫
        evaluateFunctorAt (yonedaIdentityNormalizedTargetPoint f)) := by
  have h := unstraighteningFiberHom_precompose_evaluateIso
    (representablePresheafInfinity x₀) r₀ F (yonedaRepresentableNativeEdge f) b₀
      (canonicalYonedaPointedIdentity x₀)
  have h₁ : FunctorIso
      (intervalPrecompose (functorVertex F)
          (SSet.Truncated.HomotopyCategory.homMk (yonedaRepresentableNativeEdge f).toTruncated) ≫
        canonicalYonedaTransformationFiberEvaluation x₀ F)
      (leftUnstraighteningMappingFiberHom r₀ F b₀ ≫ evaluateFunctorAt v₀) := h
  exact h₁ ≪≫ yonedaRepresentableNativeEdge_evaluationActionIso f F

end SerrePositivity.InfinityCategories.HomotopyLimits
