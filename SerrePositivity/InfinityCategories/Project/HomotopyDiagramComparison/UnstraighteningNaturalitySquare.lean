module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ConstantEdgeIntervalFamilies
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentTriangleFiberTransport

/-!
概要：元の変換空間全体を元の底の辺へ制限し、四辺を厳密に保つ自然性正方形を作る。
方針：元の共同評価の第一変数へ同じ辺を入れ、全区間族の端点公式を使う。
規約：元の二つの図式・全変換・底の辺の一単体を保持する。
使われ方：Yoneda 評価の底方向の全パラメータ自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の全変換を、元の底の指定点で評価した両端固定の同じ区間族。 -/
def unstraighteningEvaluationInterval {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app _ b) (G.app _ b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex b F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex b G)

/-- 正規化した同じ区間族は、元の全変換の区間族の同じ点での評価。 -/
lemma unstraighteningEvaluationInterval_uncurry {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (unstraighteningEvaluationInterval F G b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex b F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex b G) (𝟙 _)
  simp only [Category.id_comp] at h
  exact h

/-- 元の全変換を、元の底の同じ一本の辺へ制限した実際の自然性正方形。 -/
def unstraighteningBaseSquare {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[1] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (Δ[1] ◁ (SSet.yonedaEquiv.symm e.edge ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G))

/-- 外側始点は、元の第一図式に元の底辺を入れた同じ定値辺の族。 -/
lemma unstraighteningBaseSquare_zero {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) ≫
        unstraighteningBaseSquare F G e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (e.map F))) := by
  rw [unstraighteningBaseSquare, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_zero]
  rw [← Category.assoc, whiskerRight_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalMappingUncurry_const_edge]
  change _ ≫ (SSet.yonedaEquiv.symm e.edge ≫ F) =
    _ ≫ SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋1⦌) e.edge)
  rw [SSet.yonedaEquiv_symm_comp]

/-- 外側終点は、元の第二図式に元の底辺を入れた同じ定値辺の族。 -/
lemma unstraighteningBaseSquare_one {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) ≫
        unstraighteningBaseSquare F G e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (e.map G))) := by
  rw [unstraighteningBaseSquare, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_one]
  rw [← Category.assoc, whiskerRight_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalMappingUncurry_const_edge]
  change _ ≫ (SSet.yonedaEquiv.symm e.edge ≫ G) =
    _ ≫ SSet.yonedaEquiv.symm (G.app (Opposite.op ⦋1⦌) e.edge)
  rw [SSet.yonedaEquiv_symm_comp]

/-- 内側始点は、元の始点で元の全変換を評価した同じ区間族。 -/
lemma unstraighteningBaseSquare_inner_zero {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)) ≫
        unstraighteningBaseSquare F G e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (unstraighteningEvaluationInterval F G a) := by
  rw [unstraighteningBaseSquare, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgePrism_start_tensor, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationFamilyDiagram_evaluate,
    unstraighteningEvaluationInterval_uncurry]

/-- 内側終点は、元の終点で元の全変換を評価した同じ区間族。 -/
lemma unstraighteningBaseSquare_inner_one {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)) ≫
        unstraighteningBaseSquare F G e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (unstraighteningEvaluationInterval F G b) := by
  rw [unstraighteningBaseSquare, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgePrism_finish_tensor, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationFamilyDiagram_evaluate,
    unstraighteningEvaluationInterval_uncurry]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
