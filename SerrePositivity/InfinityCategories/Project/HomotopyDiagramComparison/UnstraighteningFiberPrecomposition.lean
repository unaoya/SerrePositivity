module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.IntervalPrecompositionTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiberHomTriangleComposition

/-!
概要：選択済みの元の区間 Hom 前合成と、元の全 fiber Hom 作用の合成を比較する。
方針：同じ前合成を長辺に持つ三角形の全族を、同じ共同評価へ送る。
規約：元の前合成と指定辺を保持し、別の合成代表の存在だけで済ませない。
使われ方：Yoneda 評価の第一変数の全パラメータ自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の関手空間内の三角形族を、同じ共同評価の三角形族へ移す。 -/
def coherentFunctorTriangleDiagram {B K : SSet.{u + 1}}
    (H : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (α_ Δ[2] B K).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism H

/-- 共同評価へ移しても、三辺は元の同じ区間族の共同評価。 -/
lemma coherentFunctorTriangleDiagram_edge {B K : SSet.{u + 1}}
    {F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (H : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (i : Fin 3) (t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)
    (hi : (stdSimplex.δ i ▷ K) ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry t) :
    (stdSimplex.δ i ▷ (B ⊗ K)) ≫ coherentFunctorTriangleDiagram H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram, ← hi]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨i, b, k⟩
  rfl

/-- 選択済みの元の区間 Hom 前合成は、同じ指定辺と全 fiber Hom の作用の合成に両立。 -/
def unstraighteningFiberHom_precomposeIso {B : SSet.{u + 1}}
    (F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (e : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)
        (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F J b)
      (lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F G b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom G J b) ≫
        MonoidalClosed.comp
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (F.app _ b))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (G.app _ b))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (J.app _ b))) := by
  let hex := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalPrecompose_triangleFamily_exists e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)
  let H := hex.choose
  have h₂ := hex.choose_spec.1
  have h₀ := hex.choose_spec.2.1
  have h₁ := hex.choose_spec.2.2
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unstraighteningFiberHom_triangleIso F G J
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e)) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)
      (SSet.Truncated.HomotopyCategory.homMk e.toTruncated))
    (coherentFunctorTriangleDiagram H)
    (coherentFunctorTriangleDiagram_edge H 2 _ h₂)
    (coherentFunctorTriangleDiagram_edge H 0 _ h₀)
    (coherentFunctorTriangleDiagram_edge H 1 _ h₁) b
  simpa only [Category.id_comp] using h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
