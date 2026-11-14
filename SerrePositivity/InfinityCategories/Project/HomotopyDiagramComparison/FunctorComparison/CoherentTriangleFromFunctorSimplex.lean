module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentTransformationVertexTriangle

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentTransformationPoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismTriangles

/-!
概要：元の関手空間の合成二単体を、同じ三辺の coherent 変換の全三角形にする。
方針：同じ二単体の評価 prism に一点パラメーターを足し、三面を厳密に照合する。
規約：長辺を充填で選び直さず、元の全二単体と全三辺を保持する。
使われ方：元の全錐の各脚の合成三角形を、全空間作用・指定余錐比較へ入力する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の辺の区間頂点による変換図式は、同じ元の辺の評価 prism。 -/
lemma coherentTransformationFamilyDiagram_of_edge {B : SSet.{u + 1}}
    {F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (e : SSet.Edge (X := (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) : (Δ[0] : SSet.{u + 1}) ⟶ _) =
        (Δ[1] ◁ fst B (Δ[0] : SSet.{u + 1})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism e := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationFamilyDiagram_const_prism,
    show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) = e from
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _]

/-- 一点パラメーター付きの三角形評価の各面は、元の同じ評価の各面。 -/
lemma functorTrianglePrismPoint_face {B X : SSet.{u + 1}}
    (q : (Δ[2] : SSet.{u + 1}) ⟶ (ihom B).obj X) (i : Fin 3) :
    (stdSimplex.δ i ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫
      ((Δ[2] : SSet.{u + 1}) ◁ fst B (Δ[0] : SSet.{u + 1})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism q =
    (Δ[1] ◁ fst B (Δ[0] : SSet.{u + 1})) ≫
      (stdSimplex.δ i ▷ B) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism q := rfl

/-- 元の関手空間の同じ合成二単体を、元の三辺を持つ全変換三角形へ移す。 -/
def coherentTransformationTriangleOfFunctorSimplex {B : SSet.{u + 1}}
    {F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    {e : SSet.Edge (X := (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)}
    {f : SSet.Edge (X := (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)}
    {g : SSet.Edge (X := (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)}
    (σ : SSet.Truncated.Edge.CompStruct e.toTruncated f.toTruncated g.toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationVertexTriangle F G J
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge f) where
  diagonal := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge g
  diagram := (Δ[2] ◁ fst B (Δ[0] : SSet.{u + 1})) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (SSet.yonedaEquiv.symm σ.simplex)
  first := by
    rw [functorTrianglePrismPoint_face, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorCompStructPrism_two σ,
      coherentTransformationFamilyDiagram_of_edge]
    rfl
  second := by
    rw [functorTrianglePrismPoint_face, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorCompStructPrism_zero σ,
      coherentTransformationFamilyDiagram_of_edge]
    rfl
  long := by
    rw [functorTrianglePrismPoint_face, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorCompStructPrism_one σ,
      coherentTransformationFamilyDiagram_of_edge]
    rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
