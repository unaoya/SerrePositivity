module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeAssociativityEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeComparisonEvaluation

/-!
概要：底全体の比較の辺の各成分を、元の底変換結合成分で計算する。
方針：転置と curry を評価し、定値パラメーターの対角評価を戻す。
規約：同じ比較の辺と同じ底変換成分を使う。
使われ方：分類主写像の結合比較の点ごとの可逆性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ底全体の比較の各成分は、元の底変換結合成分の coherent な辺。 -/
lemma cocartesianBaseChangeAssociativityEdge_at
    (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C)) (a : A) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityEdge l k) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex a)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityQCat p.val.hom l k).app a))).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex a))).app _
    (((SSet.Edge.ofTruncated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityIntervalFamily l k))).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p))).edge = _
  conv_lhs =>
    arg 2
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_edgeAt (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityIntervalFamily l k)
      (SSet.Edge.ofTruncated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p)]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex a))).app _
    ((((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrowCurry A).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityFamily l k).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p) 1))).app (Opposite.op ⦋1⦌)
          (𝟙 (Opposite.op ⦋1⦌))) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrowCurry_component]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.quasicategoryDiagramDiagonalSimplex
    (nerve.edgeMk ((homOfLE (show (0 : Fin 2) ≤ 1 by decide), 𝟙 a) :
      ((0 : Fin 2), a) ⟶ (1, a))).edge
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityDiagramComparison l k).arrowDiagram.toCoreEnrichedFunctor
      ).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p) 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramDiagonalSimplex_constant]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.qCatDiagramCoherentNerve_edge]
  have hm : (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValueFunctor
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityDiagramComparison l k).arrowDiagram.toCoreEnrichedFunctor.obj p)).map
      ((homOfLE (show (0 : Fin 2) ≤ 1 by decide), 𝟙 a) :
        ((0 : Fin 2), a) ⟶ (1, a)) = ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityQCat p.val.hom l k).app a) := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap
        (pullback.fst (nerveMap (l ⋙ k)) p.val.hom) (𝟙 a) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap_id]
    exact Category.comp_id ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom)
  exact congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) hm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
