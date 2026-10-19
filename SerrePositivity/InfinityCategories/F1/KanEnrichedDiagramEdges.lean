module

public import SerrePositivity.InfinityCategories.F1.KanEnrichedDiagram

/-!
概要：豊穣比較の図式を実現したときの辺とその可逆性。
方針：共同評価の辺を対象で評価し元の比較の射を回収する。
規約：大域的な辺の可逆性だけを点ごとの判定で検証する。
使われ方：切断の図式で始点を保つ射を同値として反転する条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：添字圏の通常の射を宇宙を揃えた nerve の辺にする。
方針：通常の nerve の辺を次数ごとに持ち上げる。
規約：両端は元の対象の標準頂点の持ち上げ。
使われ方：比較の図式の実際の辺の入力。 -/
def kanEnrichedDiagramIndexEdge {J : Type u} [Category.{u} J] {i j : J} (f : i ⟶ j) :
    SSet.Edge (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve J))
      (ULift.up (nerveVertex i)) (ULift.up (nerveVertex j)) :=
  SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f).toTruncated)

/-- 概要：比較図式の実現の辺を元の豊穣関手の頂点を両端として表示する。
方針：共同評価の添字の辺の像の端点を頂点の厳密な公式で揃える。
規約：一単体そのものは変更しない。
使われ方：関手空間の点ごとの可逆性の判定。 -/
def KanEnrichedDiagram.realizationEdge {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J)
    {i j : J} (f : i ⟶ j) :
    SSet.Edge (functorVertex (coherentNerveMap (D.obj i)))
      (functorVertex (coherentNerveMap (D.obj j))) :=
  ((kanEnrichedDiagramIndexEdge f).map (transposeFunctorFamily D.realization)).ofEq
    (by rw [transposeFunctorFamily_vertex, D.realization_evaluate])
    (by rw [transposeFunctorFamily_vertex, D.realization_evaluate])

/-- 概要：図式の実現の辺を一対象で評価すると元の比較の coherent な辺。
方針：転置、定値パラメーター、通常の図式の辺の順に評価する。
規約：一単体そのものの等式として述べる。
使われ方：全対象の比較の可逆性を反映する。 -/
lemma KanEnrichedDiagram.realization_edge_at {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J)
    {i j : J} (f : i ⟶ j) (X : C) :
    (((kanEnrichedDiagramIndexEdge f).map (transposeFunctorFamily D.realization)).map
      (evaluateFunctorAt (coherentNerveVertex X))).edge =
      (coherentNerveEdge ((D.map f).val X)).edge := by
  rw [transposeFunctorFamily_edgeAt]
  change kanDiagramDiagonalSimplex (nerve.edgeMk f).edge
    ((coherentNerveMap D.toEnrichedFunctor).app (Opposite.op ⦋1⦌)
      (PinchedHom.constant (coherentNerveVertex X) 1)) = _
  rw [pinchedConstant_map, coherentNerveMap_vertex, kanDiagramDiagonalSimplex_constant]
  exact kanDiagramCoherentNerve_edge (D.evaluate X) f

/-- 概要：全対象で同値な比較は実現した全図式の中で可逆な辺となる。
方針：任意の coherent な頂点を元の対象で表示して点ごとの判定を使う。
規約：関手や変換の等式を成分の等式から推測しない。
使われ方：切断の図式の局所化で反転する射を指定する。 -/
lemma KanEnrichedDiagram.realization_edge_isInvertible {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J)
    {i j : J} (f : i ⟶ j)
    (hf : ∀ X, IsQCatEquivalence (X := ((D.obj i).obj X).obj)
      (Y := ((D.obj j).obj X).obj) ((D.map f).val X)) :
    IsInvertibleEdge ((kanEnrichedDiagramIndexEdge f).map
      (transposeFunctorFamily D.realization)).toTruncated := by
  apply (isInvertibleEdge_congr (show
    ((kanEnrichedDiagramIndexEdge f).map (transposeFunctorFamily D.realization)).edge =
      (D.realizationEdge f).edge from rfl)).mpr
  apply (isInvertibleEdge_iff_evaluateFunctorAt (D.realizationEdge f).toTruncated).mpr
  intro s
  rw [← coherentNerveVertex_object s]
  change IsInvertibleEdge (((D.realizationEdge f).map
    (evaluateFunctorAt (coherentNerveVertex (coherentNerveObject s))))).toTruncated
  apply (isInvertibleEdge_congr (show
    (((D.realizationEdge f).map
      (evaluateFunctorAt (coherentNerveVertex (coherentNerveObject s))))).edge =
        (coherentNerveEdge ((D.map f).val (coherentNerveObject s))).edge from
          D.realization_edge_at f (coherentNerveObject s))).mpr
  exact coherentKanEdge_isInvertible_of_isQCatEquivalence (hf _)

end SerrePositivity.InfinityCategories
