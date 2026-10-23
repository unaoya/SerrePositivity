module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeComparisonRealization
public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramConstantParameter
public import SerrePositivity.InfinityCategories.F1.QCatDiagramEdges

/-!
概要：底変換比較の実際の coherent な辺の各成分は、構成済みの同じ比較成分。
方針：転置の評価を共同評価へ戻し、元の二点図式を固定した計算を使う。
規約：比較成分の別の代表や単に同値な射へ置き換えない。
使われ方：全 fibration の比較の辺の可逆性を同じ成分の同値性から検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) (d : D)

/-- 元の同じ底変換比較成分を、QCat の通常の射として表す。 -/
def cocartesianBaseChangeComparisonComponent (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianSectionsCoreEnrichedEvaluation
      (Over.mk (nerveMap (Under.forget (k.obj d))))).obj p ⟶
    (cocartesianSectionsCoreEnrichedEvaluation (Over.mk (nerveMap (Under.forget d)))).obj
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p) :=
  cocartesianStrictTransportBaseChangeComponent p.val.hom k d

/-- 同じ coherent な比較の辺を元の fibration で評価すると、元の比較成分の辺となる。 -/
lemma cocartesianBaseChangeComparisonEdge_at (p : CocartesianFibrationCategory (nerve C)) :
    (functorEdgeAt (cocartesianBaseChangeComparisonEdge k d) (coherentNerveVertex p)).edge =
      (coherentNerveEdge (cocartesianBaseChangeComparisonComponent k d p)).edge := by
  change ((coherentResolutionComparisonIndexEdge.map
    (transposeFunctorFamily (cocartesianBaseChangeComparisonRealization k d))).map
      (evaluateFunctorAt (coherentNerveVertex p))).edge = _
  rw [transposeFunctorFamily_edgeAt]
  change quasicategoryDiagramDiagonalSimplex
    (nerve.edgeMk (homOfLE
      (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≤ ULift.up 1 from by decide))).edge
    ((coherentNerveMap (cocartesianBaseChangeComparisonCoreEnriched k d)).app (Opposite.op ⦋1⦌)
      (PinchedHom.constant (coherentNerveVertex p) 1)) = _
  rw [pinchedConstant_map, coherentNerveMap_vertex, quasicategoryDiagramDiagonalSimplex_constant]
  exact qCatDiagramCoherentNerve_edge
    (quasicategoryDiagramValueFunctor ((cocartesianBaseChangeComparisonCoreEnriched k d).obj p)) _

end SerrePositivity.InfinityCategories
