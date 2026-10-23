module

public import SerrePositivity.InfinityCategories.HomotopyLimits.YonedaBaseNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalPrecompositionPostMap
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaYonedaEvaluation

/-!
概要：P_Σ の元の Yoneda 辺について、全写像空間の恒等点評価の自然性を証明する。
方針：元の包含の Hom 作用と前合成の可換性を、元の前層評価の自然性に合成する。
規約：元の Yoneda 辺・元の標的前層・同じ反変辺の標準輸送を保持する。
使われ方：元の有限余積余錐の各脚への写像空間の判定。
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

/-- 元の P_Σ 内の Yoneda の辺を、同じ二つの頂点を持つ辺として取る。 -/
def sigmaYonedaNativeEdge :
    SSet.Edge ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x₀))
      ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y₀)) :=
  (SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1}
    (((SSet.Edge.ofTruncated homotopyIntervalEdge).map f).toTruncated))).map
      (sigmaYonedaInfinityMap C)

/-- 元の P_Σ の辺の一単体は、元の Yoneda の同じ一単体の像。 -/
lemma sigmaYonedaNativeEdge_edge :
    (sigmaYonedaNativeEdge f).edge =
      (sigmaYonedaInfinityMap C).app (Opposite.op ⦋1⦌)
        (ULift.up (SSet.yonedaEquiv f)) := by
  change (sigmaYonedaInfinityMap C).app (Opposite.op ⦋1⦌)
    (ULift.up (f.app (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge)) = _
  apply congrArg ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋1⦌))
  apply congrArg ULift.up
  change f.app (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge =
    f.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  apply congrArg (f.app (Opposite.op ⦋1⦌))
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 元の包含は、元の P_Σ の Yoneda 辺を同じ元の前層 Yoneda 辺へ送る。 -/
lemma sigmaYonedaNativeEdge_inclusion :
    (sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋1⦌)
      (sigmaYonedaNativeEdge f).edge = (yonedaRepresentableNativeEdge f).edge := by
  rw [sigmaYonedaNativeEdge_edge, yonedaRepresentableNativeEdge_edge]
  exact congrArg (fun g ↦ g.app (Opposite.op ⦋1⦌) (ULift.up (SSet.yonedaEquiv f)))
    (sigmaYonedaInfinityMap_inclusion C)

/-- 元の P_Σ 内の全写像空間の評価は、元の Yoneda 辺への前合成に自然。 -/
def sigmaYonedaFiberEvaluation_naturalityIso (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    FunctorIso
      (intervalPrecompose F
          (SSet.Truncated.HomotopyCategory.homMk (sigmaYonedaNativeEdge f).toTruncated) ≫
        sigmaYonedaFiberEvaluation x₀ F)
      (sigmaYonedaFiberEvaluation y₀ F ≫ edgeTransport pointedSpaceProjection
        ((yonedaOppositeBaseEdge f).map (sigmaPresheafVertexFunctor F))) := by
  have h := intervalMappingPostOfEq_precomposeIso (sigmaPresheafInfinityInclusion C)
    (sigmaYonedaNativeEdge f) F (sigmaYonedaInfinityMap_inclusion_vertex x₀)
    (sigmaYonedaInfinityMap_inclusion_vertex y₀) (sigmaPresheafVertexFunctor_vertex F).symm
    (yonedaRepresentableNativeEdge f) (sigmaYonedaNativeEdge_inclusion f)
  have h' := h.postcomp
    (canonicalYonedaTransformationFiberEvaluation x₀ (sigmaPresheafVertexFunctor F))
  have h'' := (canonicalYonedaFiberEvaluation_naturalityIso f
    (sigmaPresheafVertexFunctor F)).precomp (sigmaYonedaTransformationComparison y₀ F)
  simp only [sigmaYonedaTransformationComparison, sigmaYonedaFiberEvaluation,
    Category.assoc] at h' h'' ⊢
  exact h' ≪≫ h''

end SerrePositivity.InfinityCategories.HomotopyLimits
