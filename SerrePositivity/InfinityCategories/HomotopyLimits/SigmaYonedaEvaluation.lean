module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaYonedaInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.CanonicalYonedaFiberTransport
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostEquivalence

/-!
概要：P_Σ 内の元の Yoneda 対象から任意の対象への写像空間を評価する。
方針：充満忠実な包含の元の区間 Hom 作用を、同じ恒等点での評価へ接続する。
規約：任意の P_Σ 頂点から元の反変関手を回収し、全パラメータの写像を保持する。
使われ方：HTT 5.5.8.10 の Yoneda の有限余積保存の写像空間判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の P_Σ 頂点が表す反変な空間値関手。 -/
def sigmaPresheafVertexFunctor {C : SSet.{u}} (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u} :=
  (presheafInfinityObjectEquiv C).symm
    ((sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) F)

/-- 回収した関手の頂点は、元の包含の同じ頂点。 -/
lemma sigmaPresheafVertexFunctor_vertex {C : SSet.{u}}
    (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    functorVertex (sigmaPresheafVertexFunctor F) =
      (sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) F :=
  (presheafInfinityObjectEquiv C).apply_symm_apply _

/-- 回収した元の関手は、空添字を含む全有限積を保存する。 -/
lemma sigmaPresheafVertexFunctor_preservesFiniteProducts {C : SSet.{u}}
    (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    PreservesFiniteProductsFromSmallSource (sigmaPresheafVertexFunctor F) :=
  sigmaPresheafInfinity_vertex F

/-- 元の Yoneda の因子化の頂点を、包含後に同じ表現可能前層へ正規化する。 -/
lemma sigmaYonedaInfinityMap_inclusion_vertex {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌) :
    (sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌)
      ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y)) =
        functorVertex (representablePresheafInfinity y) := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up y))
    (sigmaYonedaInfinityMap_inclusion C)
  exact h.trans (yonedaInfinityMap_vertex y)

/-- 包含による実際の区間 Hom 作用を、元の二つの関手頂点で表示する。 -/
def sigmaYonedaTransformationComparison {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌) (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    intervalMappingSpace
      ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y)) F ⟶
        leftUnstraighteningTransformationSpace
          (representablePresheafInfinity y) (sigmaPresheafVertexFunctor F) :=
  intervalMappingPostOfEq (sigmaPresheafInfinityInclusion C) _ _
    (sigmaYonedaInfinityMap_inclusion_vertex y) (sigmaPresheafVertexFunctor_vertex F).symm

/-- 元の包含から取った同じ区間 Hom 比較は同値。 -/
lemma sigmaYonedaTransformationComparison_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsQCatEquivalence (sigmaYonedaTransformationComparison y F) :=
  IsFullyFaithful.intervalMappingPostOfEq_isQCatEquivalence
    (sigmaPresheafInfinityInclusion_isFullyFaithful C) _ _ _ _

/-- P_Σ 内の元の写像空間を、元の Yoneda 恒等点で評価する。 -/
def sigmaYonedaFiberEvaluation {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌) (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    intervalMappingSpace
      ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y)) F ⟶
        vertexFiber pointedSpaceProjection
          ((sigmaPresheafVertexFunctor F).app (Opposite.op ⦋0⦌)
            (ULift.up (SSet.opObjEquiv.symm y))) :=
  sigmaYonedaTransformationComparison y F ≫
    canonicalYonedaTransformationFiberEvaluation y (sigmaPresheafVertexFunctor F)

/-- 任意の P_Σ 対象への同じ写像空間の恒等点評価は同値。 -/
lemma sigmaYonedaFiberEvaluation_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsQCatEquivalence (sigmaYonedaFiberEvaluation y F) :=
  (sigmaYonedaTransformationComparison_isQCatEquivalence y F).comp
    (canonicalYonedaTransformationFiberEvaluation_isQCatEquivalence y
      (sigmaPresheafVertexFunctor F))

/-- 元の評価は、同じ全変換を評価してから行う普遍輸送と全パラメータで同型。 -/
def sigmaYonedaFiberEvaluation_parametrizedIso
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    FunctorIso (sigmaYonedaFiberEvaluation y F)
      (sigmaYonedaTransformationComparison y F ≫
        intervalMappingPostOfEq (evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm y)))
          (functorVertex (representablePresheafInfinity y))
          (functorVertex (sigmaPresheafVertexFunctor F))
          (evaluateFunctorAt_functorVertex _ _) (evaluateFunctorAt_functorVertex _ _) ≫
        parametrizedFiberTransport pointedSpaceProjection
          ((representablePresheafInfinity y).app _ (ULift.up (SSet.opObjEquiv.symm y)))
          ((sigmaPresheafVertexFunctor F).app _ (ULift.up (SSet.opObjEquiv.symm y))) ≫
        evaluateFunctorAt (canonicalYonedaPointedIdentity y)) := by
  have h := (canonicalYonedaTransformationFiberEvaluation_parametrizedIso y
    (sigmaPresheafVertexFunctor F)).precomp (sigmaYonedaTransformationComparison y F)
  simpa only [sigmaYonedaFiberEvaluation, Category.assoc] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
