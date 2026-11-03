module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFamilyPrism
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostIso
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostcompositionVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.ElementsDiagram
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.HomotopyTransformationVertex
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityDiagramHomotopy
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityRestrictedHomotopy
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityRestrictedTransformation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensitySourceRestriction
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityTransformation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafTwistedElementsMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedElementsReconstruction
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.Ind.CanonicalIntervalYonedaValue
public import SerrePositivity.InfinityCategories.F1.Ind.DensityFiberTransformationFamily
public import SerrePositivity.InfinityCategories.F1.Ind.DensityIdentityLift
public import SerrePositivity.InfinityCategories.F1.Ind.DensityOriginalFiberPrism
public import SerrePositivity.InfinityCategories.F1.Ind.ElementsYonedaSliceInterval
public import SerrePositivity.InfinityCategories.F1.Ind.MappingVertexLiftPrism
public import SerrePositivity.InfinityCategories.F1.Ind.PresheafDensityIdentityReconstruction

/-!
概要：恒等点復元射上の元の密度持ち上げの底は、同じ canonical な評価区間の全族。
方針：元の復元射の射影、密度変換の評価、区間作用の全円柱の読み戻しを使う。
規約：全 fiber パラメータ上の厳密な等式。
使われ方：同じ始値・同じ底の持ち上げの終値の選択独立性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "A" => presheafDensityFiberParameter F x
local notation "E" => presheafDensityElementsParameter F
local notation "i" => presheafDensityFiberParameterInclusion F x

/-- 同じ持ち上げの底は、元の大域密度変換を同じ対象で評価した区間族そのもの。 -/
lemma presheafDensityIdentityLiftPrism_projection :
    presheafDensityIdentityLiftPrism F x ≫ pointedSpaceProjection =
      intervalMappingUncurry (presheafDensityCanonicalFiberInterval F x) := by
  rw [presheafDensityIdentityLiftPrism, mappingVertexLiftPrism_projection,
    presheafDensityIdentityReconstruction_projection,
    presheafDensityCanonicalFiberInterval, intervalMappingPostOfEq_uncurry,
    presheafDensityOriginalFiberInterval_prism]
  change (Δ[1] ◁ i) ≫ functorEdgePrism
    (intervalMappingEdgeOfVertex (presheafDensityEvaluatedTransformationVertex F x)) = _
  have hh : functorEdgePrism
      (intervalMappingEdgeOfVertex (presheafDensityEvaluatedTransformationVertex F x)) =
      (β_ Δ[1] E).hom ≫ (presheafDensityRestrictedHomotopy F x).h := by
    rw [presheafDensityEvaluatedTransformationVertex_restriction,
      presheafDensityRestrictedTransformationVertex]
    change (β_ Δ[1] E).hom ≫
      (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex
        (homotopyTransformationVertex (presheafDensityRestrictedHomotopy F x))).toTruncated).h = _
    rw [homotopyTransformationVertex_h]
  rw [hh]
  have he := presheafDensityDiagramHomotopy_evaluation F x
  change (presheafDensityDiagramHomotopy F).h ≫
    evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x)) =
      (presheafDensityRestrictedHomotopy F x).h at he
  rw [← he]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.F2.Ind
