module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UnstraighteningBaseTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.YonedaEvaluationPrecomposition
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge

/-!
概要：元の Yoneda 脚の前合成と、標的前層の元の反変辺による輸送の自然性。
方針：元の反転辺の表示を揃え、二つの全パラメータ評価比較を合成する。
規約：元の前合成・元の Yoneda 辺・恒等点・標的の元の辺を保持する。
使われ方：P_Σ 内の同じ有限余積余錐の脚への写像空間の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {C : SSet.{u}} [Quasicategory C] (f : (Δ[1] : SSet.{u}) ⟶ C)
local notation "x₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
local notation "y₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)
local notation "r₀" => representablePresheafInfinity y₀
local notation "a₀" => ULift.up (SSet.opObjEquiv.symm y₀)
local notation "b₀" => ULift.up (SSet.opObjEquiv.symm x₀)

/-- 元の一本の辺の反転を、元の持ち上げた反対圏内の同じ辺として保持する。 -/
def yonedaOppositeBaseEdge :
    SSet.Edge (X := (SSet.uliftFunctor.{u + 1, u}).obj C.op) a₀ b₀ :=
  SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1}
    (edgeOp ((SSet.Edge.ofTruncated homotopyIntervalEdge).map f).toTruncated))

omit [Quasicategory C] in
/-- 持ち上げた反転辺の一単体は、元の辺の一単体の同じ反転。 -/
lemma yonedaOppositeBaseEdge_edge :
    (yonedaOppositeBaseEdge f).edge = ULift.up (SSet.opObjEquiv.symm (SSet.yonedaEquiv f)) := by
  change ULift.up (SSet.opObjEquiv.symm (f.app (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge)) = _
  apply congrArg (fun t ↦ ULift.up (SSet.opObjEquiv.symm t))
  change f.app (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge =
    f.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  apply congrArg (f.app (Opposite.op ⦋1⦌))
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 元の反転辺の表現可能前層での像は、同じ恒等点輸送の元の反変辺。 -/
lemma yonedaOppositeBaseEdge_representable :
    (yonedaOppositeBaseEdge f).map r₀ = yonedaIdentityNormalizedTargetEdge f := by
  apply SSet.Edge.ext
  change (representablePresheafInfinity y₀).app (Opposite.op ⦋1⦌)
    (yonedaOppositeBaseEdge f).edge = (yonedaIdentityNormalizedTargetEdge f).edge
  rw [yonedaOppositeBaseEdge_edge, yonedaIdentityNormalizedTargetEdge_edge]

/-- 反変輸送点での元の全評価は、終点の同じ Yoneda 評価の後の標的の元の輸送と同型。 -/
def canonicalYonedaFiberEvaluation_baseIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    FunctorIso
      (leftUnstraighteningMappingFiberHom r₀ F b₀ ≫
        evaluateFunctorAt (yonedaIdentityNormalizedTargetPoint f))
      (canonicalYonedaTransformationFiberEvaluation y₀ F ≫
        edgeTransport pointedSpaceProjection ((yonedaOppositeBaseEdge f).map F)) := by
  have h := unstraighteningFiberEvaluation_baseTransportIso r₀ F
    (yonedaOppositeBaseEdge f) (canonicalYonedaPointedIdentity y₀)
  rw [yonedaOppositeBaseEdge_representable] at h
  exact h

/-- 元の Yoneda 脚への前合成と標的の元の反変辺への輸送は、全写像空間で自然。 -/
def canonicalYonedaFiberEvaluation_naturalityIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    FunctorIso
      (intervalPrecompose (functorVertex F)
          (SSet.Truncated.HomotopyCategory.homMk (yonedaRepresentableNativeEdge f).toTruncated) ≫
        canonicalYonedaTransformationFiberEvaluation x₀ F)
      (canonicalYonedaTransformationFiberEvaluation y₀ F ≫
        edgeTransport pointedSpaceProjection ((yonedaOppositeBaseEdge f).map F)) :=
  canonicalYonedaFiberEvaluation_precomposeIso f F ≪≫ canonicalYonedaFiberEvaluation_baseIso f F

end SerrePositivity.InfinityCategories.HomotopyLimits
