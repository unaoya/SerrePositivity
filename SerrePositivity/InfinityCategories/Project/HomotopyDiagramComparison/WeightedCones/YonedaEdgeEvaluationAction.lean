module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.PointEvaluationFunctor
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.YonedaRepresentableEdgeEvaluation

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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

variable {C : SSet.{u}} [Quasicategory C] (f : (Δ[1] : SSet.{u}) ⟶ C)
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
local notation "x₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
local notation "y₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)
local notation "b₀" => ULift.up (SSet.opObjEquiv.symm x₀)
local notation "r₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y₀
local notation "v₀" => NatTrans.app
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaTransformationFiberEvaluation x₀ r₀) (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaRepresentableNativeEdge f))

/-- 同じ恒等点像と反変輸送点の比較は、任意の標的への全変換の評価と両立する。 -/
def yonedaRepresentableNativeEdge_evaluationActionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom r₀ F b₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v₀)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom r₀ F b₀ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityNormalizedTargetPoint f)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.evaluateFunctorAt_vertexIso
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (NatTrans.app r₀ (Opposite.op ⦋0⦌) b₀))
    (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b₀))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaRepresentableNativeEdge_evaluationIso f)).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom r₀ F b₀)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
