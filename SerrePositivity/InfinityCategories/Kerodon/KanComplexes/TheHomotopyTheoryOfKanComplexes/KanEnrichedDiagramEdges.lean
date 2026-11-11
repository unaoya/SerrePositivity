module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram

/-!
概要：豊穣比較の図式を実現したときの辺とその可逆性。
方針：共同評価の辺を対象で評価し元の比較の射を回収する。
規約：大域的な辺の可逆性だけを点ごとの判定で検証する。
使われ方：切断の図式で始点を保つ射を同値として反転する条件。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：添字圏の通常の射を宇宙を揃えた nerve の辺にする。
方針：通常の nerve の辺を次数ごとに持ち上げる。
規約：両端は元の対象の標準頂点の持ち上げ。
使われ方：比較の図式の実際の辺の入力。 -/
def kanEnrichedDiagramIndexEdge {J : Type u} [Category.{u} J] {i j : J} (f : i ⟶ j) :
    SSet.Edge (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve J))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)) :=
  SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f).toTruncated)

/-- 概要：比較図式の実現の辺を元の豊穣関手の頂点を両端として表示する。
方針：共同評価の添字の辺の像の端点を頂点の厳密な公式で揃える。
規約：一単体そのものは変更しない。
使われ方：関手空間の点ごとの可逆性の判定。 -/
def KanEnrichedDiagram.realizationEdge {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J)
    {i j : J} (f : i ⟶ j) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (D.obj i)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (D.obj j))) :=
  ((kanEnrichedDiagramIndexEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily D.realization)).ofEq
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_vertex, D.realization_evaluate])
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_vertex, D.realization_evaluate])

/-- 概要：図式の実現の辺を一対象で評価すると元の比較の coherent な辺。
方針：転置、定値パラメーター、通常の図式の辺の順に評価する。
規約：一単体そのものの等式として述べる。
使われ方：全対象の比較の可逆性を反映する。 -/
lemma KanEnrichedDiagram.realization_edge_at {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J)
    {i j : J} (f : i ⟶ j) (X : C) :
    (((kanEnrichedDiagramIndexEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily D.realization)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((D.map f).val X)).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_edgeAt]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramDiagonalSimplex (nerve.edgeMk f).edge
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap D.toEnrichedFunctor).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramDiagonalSimplex_constant]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_edge (D.evaluate X) f

/-- 概要：全対象で同値な比較は実現した全図式の中で可逆な辺となる。
方針：任意の coherent な頂点を元の対象で表示して点ごとの判定を使う。
規約：関手や変換の等式を成分の等式から推測しない。
使われ方：切断の図式の局所化で反転する射を指定する。 -/
lemma KanEnrichedDiagram.realization_edge_isInvertible {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J)
    {i j : J} (f : i ⟶ j)
    (hf : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := ((D.obj i).obj X).obj)
      (Y := ((D.obj j).obj X).obj) ((D.map f).val X)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((kanEnrichedDiagramIndexEdge f).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily D.realization)).toTruncated := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    ((kanEnrichedDiagramIndexEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily D.realization)).edge =
      (D.realizationEdge f).edge from rfl)).mpr
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt (D.realizationEdge f).toTruncated).mpr
  intro s
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object s]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (((D.realizationEdge f).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject s))))).toTruncated
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    (((D.realizationEdge f).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject s))))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((D.map f).val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject s))).edge from
          D.realization_edge_at f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject s))).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence (hf _)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
