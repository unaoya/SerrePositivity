module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaYonedaInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CanonicalYonedaFiberTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostEquivalence

/-!
概要：P_Σ 内の元の Yoneda 対象から任意の対象への写像空間を評価する。
方針：充満忠実な包含の元の区間 Hom 作用を、同じ恒等点での評価へ接続する。
規約：任意の P_Σ 頂点から元の反変関手を回収し、全パラメータの写像を保持する。
使われ方：HTT 5.5.8.10 の Yoneda の有限余積保存の写像空間判定。

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

/-- 元の P_Σ 頂点が表す反変な空間値関手。 -/
def sigmaPresheafVertexFunctor {C : SSet.{u}} (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) F)

/-- 回収した関手の頂点は、元の包含の同じ頂点。 -/
lemma sigmaPresheafVertexFunctor_vertex {C : SSet.{u}}
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (sigmaPresheafVertexFunctor F) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) F :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).apply_symm_apply _

/-- 回収した元の関手は、空添字を含む全有限積を保存する。 -/
lemma sigmaPresheafVertexFunctor_preservesFiniteProducts {C : SSet.{u}}
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PreservesFiniteProductsFromSmallSource (sigmaPresheafVertexFunctor F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinity_vertex F

/-- 元の Yoneda の因子化の頂点を、包含後に同じ表現可能前層へ正規化する。 -/
lemma sigmaYonedaInfinityMap_inclusion_vertex {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap_inclusion C)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_vertex y)

/-- 包含による実際の区間 Hom 作用を、元の二つの関手頂点で表示する。 -/
def sigmaYonedaTransformationComparison {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌) (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y)) F ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) (sigmaPresheafVertexFunctor F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) _ _
    (sigmaYonedaInfinityMap_inclusion_vertex y) (sigmaPresheafVertexFunctor_vertex F).symm

/-- 元の包含から取った同じ区間 Hom 比較は同値。 -/
lemma sigmaYonedaTransformationComparison_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (sigmaYonedaTransformationComparison y F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsFullyFaithful.intervalMappingPostOfEq_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion_isFullyFaithful C) _ _ _ _

/-- P_Σ 内の元の写像空間を、元の Yoneda 恒等点で評価する。 -/
def sigmaYonedaFiberEvaluation {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌) (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y)) F ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
          ((sigmaPresheafVertexFunctor F).app (Opposite.op ⦋0⦌)
            (ULift.up (SSet.opObjEquiv.symm y))) :=
  sigmaYonedaTransformationComparison y F ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaTransformationFiberEvaluation y (sigmaPresheafVertexFunctor F)

/-- 任意の P_Σ 対象への同じ写像空間の恒等点評価は同値。 -/
lemma sigmaYonedaFiberEvaluation_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (sigmaYonedaFiberEvaluation y F) :=
  (sigmaYonedaTransformationComparison_isQCatEquivalence y F).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaTransformationFiberEvaluation_isQCatEquivalence y
      (sigmaPresheafVertexFunctor F))

/-- 元の評価は、同じ全変換を評価してから行う普遍輸送と全パラメータで同型。 -/
def sigmaYonedaFiberEvaluation_parametrizedIso
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (sigmaYonedaFiberEvaluation y F)
      (sigmaYonedaTransformationComparison y F ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm y)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (sigmaPresheafVertexFunctor F))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex _ _) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y).app _ (ULift.up (SSet.opObjEquiv.symm y)))
          ((sigmaPresheafVertexFunctor F).app _ (ULift.up (SSet.opObjEquiv.symm y))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity y)) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaTransformationFiberEvaluation_parametrizedIso y
    (sigmaPresheafVertexFunctor F)).precomp (sigmaYonedaTransformationComparison y F)
  simpa only [sigmaYonedaFiberEvaluation, Category.assoc] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
