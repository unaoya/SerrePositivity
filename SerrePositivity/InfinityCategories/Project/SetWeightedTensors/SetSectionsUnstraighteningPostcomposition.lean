module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.IntervalPostcompositionTriangle
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorCompositionFixedTarget
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningEdgeLiftFamily

/-!
概要：指定辺の後合成と unstraightening の相対合成を全族で比較する。
方針：指定三辺の三角形族を既存の相対合成比較へ渡す。
規約：元の後合成と辺を保持する。
使われ方：G14 の Yoneda 評価の標的自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

/-- 指定辺の後合成を元の全空間の相対合成と比較する全パラメータの同型。 -/
def unstraighteningPostcompositionIso {B : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex G) (functorVertex J)) :
    FunctorIso
      (intervalPostcompose (functorVertex F)
          (Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        leftUnstraighteningMappingSpaceMap F J)
      (lift
        (leftUnstraighteningMappingSpaceMap F G)
        (SSet.const (intervalMappingVertexOfEdge e) ≫ leftUnstraighteningMappingSpaceMap G J) ≫
        relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
          (Over.mk (leftUnstraighteningProjection G))
          (Over.mk (leftUnstraighteningProjection J))) := by
  let h := intervalPostcompose_triangleFamily_exists (functorVertex F) e
  let H := Classical.choose h
  have h₀₁ := (Classical.choose_spec h).1
  have h₁₂ := (Classical.choose_spec h).2.1
  have h₀₂ := (Classical.choose_spec h).2.2
  let K := leftUnstraighteningTransformationSpace F G
  let W : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u} :=
    (α_ Δ[2] B K).inv ≫ functorParameterizedPrism H
  have hw₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ W =
      coherentTransformationFamilyDiagram (𝟙 K) := by
    exact (SetWeight.parameterizedDiagram_face H 2).trans
      (congrArg (fun T => (α_ Δ[1] B K).inv ≫ functorParameterizedPrism T) h₀₁)
  have hw₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ W =
      coherentTransformationFamilyDiagram (SSet.const (intervalMappingVertexOfEdge e) : K ⟶ _) := by
    exact (SetWeight.parameterizedDiagram_face H 0).trans
      (congrArg (fun T => (α_ Δ[1] B K).inv ≫ functorParameterizedPrism T) h₁₂)
  have hw₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ W =
      coherentTransformationFamilyDiagram
        (intervalPostcompose (functorVertex F)
          (Truncated.HomotopyCategory.homMk e.toTruncated)) := by
    exact (SetWeight.parameterizedDiagram_face H 1).trans
      (congrArg (fun T => (α_ Δ[1] B K).inv ≫ functorParameterizedPrism T) h₀₂)
  simpa only [Category.id_comp] using unstraighteningMappingTriangleIso F G J
    (𝟙 K) (SSet.const (intervalMappingVertexOfEdge e))
    (intervalPostcompose (functorVertex F)
      (Truncated.HomotopyCategory.homMk e.toTruncated)) W hw₀₁ hw₁₂ hw₀₂


/-- 元の pinched 後合成は、同じ辺の実際の持ち上げによる相対後合成と全族で同型。 -/
def unstraighteningPinchedEdgeLiftPostcompositionIso {B : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex G) (functorVertex J)) :
    FunctorIso
      (postcompose (functorVertex F) (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        leftUnstraighteningPinchedMappingSpaceMap F J)
      (leftUnstraighteningPinchedMappingSpaceMap F G ≫
        SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost
          (leftUnstraighteningProjection G) (leftUnstraighteningProjection J)
          (leftUnstraighteningEdgeLiftMap G J e)
          (leftUnstraighteningEdgeLiftMap_projection G J e) (leftUnstraighteningProjection F)) := by
  have h := (liftMapComparisonIso
    (intervalPostcompose (functorVertex F)
      (SSet.Truncated.HomotopyCategory.homMk e.toTruncated))).postcomp
        (leftUnstraighteningMappingSpaceMap F J)
  have k := (unstraighteningPostcompositionIso F G J e).precomp
    (pinchedHomToIntervalMappingSpace (functorVertex F) (functorVertex G))
  have h' : FunctorIso
      (postcompose (functorVertex F) (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        leftUnstraighteningPinchedMappingSpaceMap F J)
      (pinchedHomToIntervalMappingSpace (functorVertex F) (functorVertex G) ≫
        lift (leftUnstraighteningMappingSpaceMap F G)
          (SSet.const (intervalMappingVertexOfEdge e) ≫ leftUnstraighteningMappingSpaceMap G J) ≫
            relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
              (Over.mk (leftUnstraighteningProjection G))
              (Over.mk (leftUnstraighteningProjection J))) := by
    simpa only [leftUnstraighteningPinchedMappingSpaceMap, postcompose, Category.assoc]
      using h ≪≫ k
  simp only [SSet.const_comp] at h'
  erw [leftUnstraighteningEdgeLiftMap_vertex G J e] at h'
  let f : Over.mk (leftUnstraighteningProjection G) ⟶
      Over.mk (leftUnstraighteningProjection J) :=
    Over.homMk (leftUnstraighteningEdgeLiftMap G J e)
      (leftUnstraighteningEdgeLiftMap_projection G J e)
  erw [relativeFunctorComposition_const_second (Over.mk (leftUnstraighteningProjection F))
    _ _ f (leftUnstraighteningMappingSpaceMap F G)] at h'
  dsimp only [f, Over.mk, Over.hom, CostructuredArrow.mk, Over.homMk, Over.Hom.left, CostructuredArrow.homMk] at h'
  simpa only [leftUnstraighteningPinchedMappingSpaceMap, Category.assoc] using h'

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
