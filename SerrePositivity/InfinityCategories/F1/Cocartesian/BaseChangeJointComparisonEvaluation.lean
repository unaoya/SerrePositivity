module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeJointComparisonEdge
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeComparisonEvaluation

/-!
概要：底全体の比較の辺の各成分を、元の底変換比較成分で計算する。
方針：転置と curry を評価し、定値パラメーターの対角評価を戻す。
規約：同じ比較の辺と同じ底変換成分を使う。
使われ方：分類主写像の底変換比較の点ごとの可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)

/-- 同じ底全体の比較の各成分は、元の底変換比較成分の coherent な辺。 -/
lemma cocartesianBaseChangeJointComparisonEdge_at
    (p : CocartesianFibrationCategory (nerve C)) (d : D) :
    ((functorEdgeAt (cocartesianBaseChangeJointComparisonEdge k) (coherentNerveVertex p)).map
      (evaluateFunctorAt (ULift.up (nerveVertex d)))).edge =
      (coherentNerveEdge (cocartesianBaseChangeComparisonComponent k d p)).edge := by
  change (evaluateFunctorAt (ULift.up (nerveVertex d))).app _
    (((SSet.Edge.ofTruncated homotopyIntervalEdge).map
    (transposeFunctorFamily (cocartesianBaseChangeJointIntervalFamily k))).map
      (evaluateFunctorAt (coherentNerveVertex p))).edge = _
  conv_lhs =>
    arg 2
    rw [transposeFunctorFamily_edgeAt (cocartesianBaseChangeJointIntervalFamily k)
      (SSet.Edge.ofTruncated homotopyIntervalEdge) (coherentNerveVertex p)]
  change (evaluateFunctorAt (ULift.up (nerveVertex d))).app _
    ((((qCatDiagramArrowCurry D).app _
      ((cocartesianBaseChangeJointComparisonFamily k).app (Opposite.op ⦋1⦌)
        (PinchedHom.constant (coherentNerveVertex p) 1))).app (Opposite.op ⦋1⦌)
          (𝟙 (Opposite.op ⦋1⦌))) homotopyIntervalEdge.edge) = _
  rw [qCatDiagramArrowCurry_component]
  change quasicategoryDiagramDiagonalSimplex
    (nerve.edgeMk ((homOfLE (show (0 : Fin 2) ≤ 1 by decide), 𝟙 d) :
      ((0 : Fin 2), d) ⟶ (1, d))).edge
    ((coherentNerveMap (cocartesianBaseChangeDiagramComparison k).arrowDiagram.toCoreEnrichedFunctor
      ).app (Opposite.op ⦋1⦌) (PinchedHom.constant (coherentNerveVertex p) 1)) = _
  rw [pinchedConstant_map, coherentNerveMap_vertex,
    quasicategoryDiagramDiagonalSimplex_constant]
  rw [qCatDiagramCoherentNerve_edge]
  have hm : (quasicategoryDiagramValueFunctor
      ((cocartesianBaseChangeDiagramComparison k).arrowDiagram.toCoreEnrichedFunctor.obj p)).map
      ((homOfLE (show (0 : Fin 2) ≤ 1 by decide), 𝟙 d) :
        ((0 : Fin 2), d) ⟶ (1, d)) = cocartesianBaseChangeComparisonComponent k d p := by
    change cocartesianStrictTransportBaseChangeComponent p.val.hom k d ≫
      kanCocartesianStrictTransportMap
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom (𝟙 d) = _
    rw [kanCocartesianStrictTransportMap_id]
    exact Category.comp_id (cocartesianStrictTransportBaseChangeComponent p.val.hom k d)
  exact congrArg (fun f ↦ (coherentNerveEdge f).edge) hm

end SerrePositivity.InfinityCategories
