module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityEdge
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeComparisonEvaluation

/-!
概要：底全体の比較の辺の各成分を、元の底変換結合成分で計算する。
方針：転置と curry を評価し、定値パラメーターの対角評価を戻す。
規約：同じ比較の辺と同じ底変換成分を使う。
使われ方：分類主写像の結合比較の点ごとの可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ底全体の比較の各成分は、元の底変換結合成分の coherent な辺。 -/
lemma cocartesianBaseChangeAssociativityEdge_at
    (p : CocartesianFibrationCategory (nerve C)) (a : A) :
    ((functorEdgeAt (cocartesianBaseChangeAssociativityEdge l k) (coherentNerveVertex p)).map
      (evaluateFunctorAt (ULift.up (nerveVertex a)))).edge =
      (coherentNerveEdge (((cocartesianBaseChangeAssociativityQCat p.val.hom l k).app a))).edge := by
  change (evaluateFunctorAt (ULift.up (nerveVertex a))).app _
    (((SSet.Edge.ofTruncated homotopyIntervalEdge).map
    (transposeFunctorFamily (cocartesianBaseChangeAssociativityIntervalFamily l k))).map
      (evaluateFunctorAt (coherentNerveVertex p))).edge = _
  conv_lhs =>
    arg 2
    rw [transposeFunctorFamily_edgeAt (cocartesianBaseChangeAssociativityIntervalFamily l k)
      (SSet.Edge.ofTruncated homotopyIntervalEdge) (coherentNerveVertex p)]
  change (evaluateFunctorAt (ULift.up (nerveVertex a))).app _
    ((((qCatDiagramArrowCurry A).app _
      ((cocartesianBaseChangeAssociativityFamily l k).app (Opposite.op ⦋1⦌)
        (PinchedHom.constant (coherentNerveVertex p) 1))).app (Opposite.op ⦋1⦌)
          (𝟙 (Opposite.op ⦋1⦌))) homotopyIntervalEdge.edge) = _
  rw [qCatDiagramArrowCurry_component]
  change quasicategoryDiagramDiagonalSimplex
    (nerve.edgeMk ((homOfLE (show (0 : Fin 2) ≤ 1 by decide), 𝟙 a) :
      ((0 : Fin 2), a) ⟶ (1, a))).edge
    ((coherentNerveMap (cocartesianBaseChangeAssociativityDiagramComparison l k).arrowDiagram.toCoreEnrichedFunctor
      ).app (Opposite.op ⦋1⦌) (PinchedHom.constant (coherentNerveVertex p) 1)) = _
  rw [pinchedConstant_map, coherentNerveMap_vertex,
    quasicategoryDiagramDiagonalSimplex_constant]
  rw [qCatDiagramCoherentNerve_edge]
  have hm : (quasicategoryDiagramValueFunctor
      ((cocartesianBaseChangeAssociativityDiagramComparison l k).arrowDiagram.toCoreEnrichedFunctor.obj p)).map
      ((homOfLE (show (0 : Fin 2) ≤ 1 by decide), 𝟙 a) :
        ((0 : Fin 2), a) ⟶ (1, a)) = ((cocartesianBaseChangeAssociativityQCat p.val.hom l k).app a) := by
    change (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom ≫
      kanCocartesianStrictTransportMap
        (pullback.fst (nerveMap (l ⋙ k)) p.val.hom) (𝟙 a) = _
    rw [kanCocartesianStrictTransportMap_id]
    exact Category.comp_id ((cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom)
  exact congrArg (fun f ↦ (coherentNerveEdge f).edge) hm

end SerrePositivity.InfinityCategories
