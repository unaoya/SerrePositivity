module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaBaseNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.IntervalPrecompositionPostMap
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaYonedaEvaluation

/-!
概要：P_Σ の元の Yoneda 辺について、全写像空間の恒等点評価の自然性を証明する。
方針：元の包含の Hom 作用と前合成の可換性を、元の前層評価の自然性に合成する。
規約：元の Yoneda 辺・元の標的前層・同じ反変辺の標準輸送を保持する。
使われ方：元の有限余積余錐の各脚への写像空間の判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u}} [Quasicategory C] (f : (Δ[1] : SSet.{u}) ⟶ C)
local notation "x₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
local notation "y₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)

/-- 元の P_Σ 内の Yoneda の辺を、同じ二つの頂点を持つ辺として取る。 -/
def sigmaYonedaNativeEdge :
    SSet.Edge ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x₀))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y₀)) :=
  (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1}
    (((SSet.Edge.ofTruncated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map f).toTruncated))).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)

/-- 元の P_Σ の辺の一単体は、元の Yoneda の同じ一単体の像。 -/
lemma sigmaYonedaNativeEdge_edge :
    (sigmaYonedaNativeEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app (Opposite.op ⦋1⦌)
        (ULift.up (SSet.yonedaEquiv f)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app (Opposite.op ⦋1⦌)
    (ULift.up (f.app (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) = _
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app (Opposite.op ⦋1⦌))
  apply congrArg ULift.up
  change f.app (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge =
    f.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  apply congrArg (f.app (Opposite.op ⦋1⦌))
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 元の包含は、元の P_Σ の Yoneda 辺を同じ元の前層 Yoneda 辺へ送る。 -/
lemma sigmaYonedaNativeEdge_inclusion :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋1⦌)
      (sigmaYonedaNativeEdge f).edge = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaRepresentableNativeEdge f).edge := by
  rw [sigmaYonedaNativeEdge_edge, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaRepresentableNativeEdge_edge]
  exact congrArg (fun g ↦ g.app (Opposite.op ⦋1⦌) (ULift.up (SSet.yonedaEquiv f)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap_inclusion C)

/-- 元の P_Σ 内の全写像空間の評価は、元の Yoneda 辺への前合成に自然。 -/
def sigmaYonedaFiberEvaluation_naturalityIso (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose F
          (SSet.Truncated.HomotopyCategory.homMk (sigmaYonedaNativeEdge f).toTruncated) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaFiberEvaluation x₀ F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaFiberEvaluation y₀ F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaOppositeBaseEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor F))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalMappingPostOfEq_precomposeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C)
    (sigmaYonedaNativeEdge f) F (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap_inclusion_vertex x₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap_inclusion_vertex y₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor_vertex F).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaRepresentableNativeEdge f) (sigmaYonedaNativeEdge_inclusion f)
  have h' := h.postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaTransformationFiberEvaluation x₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor F))
  have h'' := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.canonicalYonedaFiberEvaluation_naturalityIso f
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor F)).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaTransformationComparison y₀ F)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaTransformationComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaFiberEvaluation,
    Category.assoc] at h' h'' ⊢
  exact h' ≪≫ h''

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
