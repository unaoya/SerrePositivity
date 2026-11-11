module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentTriangleFiberTransport

/-!
概要：元の全 fiber Hom 比較は coherent な三角形の全族の合成と両立する。
方針：元の同じ三角形を各点で評価し、元の二辺の輸送族の合成を使う。
規約：写像空間全体の関手同型を構成し、個々の変換での合成同型に弱めない。
使われ方：Yoneda の元の前合成族と、恒等点評価の第一変数の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の全 fiber Hom 比較の合成則を、同じ coherent 三角形の全族で証明する。 -/
def unstraighteningFiberHom_triangleIso {B K : SSet.{u + 1}}
    (F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (t₀₁ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)
    (t₁₂ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace G J)
    (t₀₂ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F J)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₂ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₁)
    (h₀ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₁₂)
    (h₁ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₂) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (t₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F J b)
      (lift (t₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F G b)
        (t₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom G J b) ≫
        MonoidalClosed.comp
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (F.app _ b))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (G.app _ b))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (J.app _ b))) := by
  let U := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTriangleFiberTransportFamily F G H b 2 t₀₁ h₂
  let V := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTriangleFiberTransportFamily G J H b 0 t₁₂ h₀
  let W := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTriangleFiberTransportFamily F J H b 1 t₀₂ h₁
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫
      ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTriangleEvaluate H b) =
      SSet.const (J.app _ b) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTriangleEvaluate_edge H b 1 t₀₂ h₁, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one, SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fiberTransportFamilyTriangle_mapIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTriangleEvaluate H b) U V W hc
  simpa only [U, V, W, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTriangleFiberTransportFamily_map] using h

/-- 元の任意の二つの変換族は、全 fiber 作用の合成と両立する同じ三角形族へ延長できる。 -/
lemma unstraighteningFiberHom_compositionFamily_exists {B K : SSet.{u + 1}}
    (F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (t₀₁ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)
    (t₁₂ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace G J) (b : B _⦋0⦌) :
    ∃ (t₀₂ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F J)
      (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
      (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₁ ∧
      (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₁₂ ∧
      (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₂ ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (t₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F J b)
        (lift (t₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F G b)
          (t₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom G J b) ≫
          MonoidalClosed.comp
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (F.app _ b))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (G.app _ b))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (J.app _ b)))) := by
  obtain ⟨t₀₂, H, h₂, h₀, h₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyTriangle_nonempty t₀₁ t₁₂
  exact ⟨t₀₂, H, h₂, h₀, h₁,
    ⟨unstraighteningFiberHom_triangleIso F G J t₀₁ t₁₂ t₀₂ H h₂ h₀ h₁ b⟩⟩

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
