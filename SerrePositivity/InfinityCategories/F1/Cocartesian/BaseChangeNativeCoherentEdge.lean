module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeDiagramHom
public import SerrePositivity.InfinityCategories.F1.CoherentNerveHomEdgeNaturality

/-!
概要：元の全空間の結合同型の分類像の辺は、底全体の既存の結合比較を実現した辺。
方針：元の図式値豊穣像の厳密な一致を coherent nerve の一単体へ移す。
規約：底の頂点での一致に限定せず、分類先の図式全体の元の辺を保持する。
使われ方：同じ結合共役の分類像と既存の Hom 輸送を結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C))

/-- 元の結合同型の図式値豊穣像の coherent な辺は、同じ strict 結合比較の元の辺。 -/
lemma cocartesianBaseChangeNativeObjectIso_diagram_edge :
    (coherentNerveMap (cocartesianStrictTransportEnrichedDiagram A).toCoreEnrichedFunctor).app
      (Opposite.op ⦋1⦌) (coherentNerveEdge (cocartesianBaseChangeNativeObjectIso l k p).hom).edge =
    (coherentNerveEdge (cocartesianBaseChangeNativeDiagramHom l k p)).edge :=
  coherentNerveMap_edge_of_homEquiv
    (cocartesianStrictTransportEnrichedDiagram A).toCoreEnrichedFunctor
    (cocartesianBaseChangeNativeObjectIso l k p).hom
    (cocartesianBaseChangeNativeDiagramHom l k p)
    (cocartesianBaseChangeNativeDiagramHom_enriched l k p)

/-- 同じ分類主写像による結合同型の像は、底全体の同じ strict 結合比較の実現。 -/
lemma cocartesianBaseChangeNativeObjectIso_classified_edge :
    (cocartesianStraighteningCoherentMap A).app (Opposite.op ⦋1⦌)
      (coherentNerveEdge (cocartesianBaseChangeNativeObjectIso l k p).hom).edge =
    (quasicategoryDiagramRealization A).app (Opposite.op ⦋1⦌)
      (coherentNerveEdge (cocartesianBaseChangeNativeDiagramHom l k p)).edge := by
  have h := congrArg ((quasicategoryDiagramRealization A).app (Opposite.op ⦋1⦌))
    (cocartesianBaseChangeNativeObjectIso_diagram_edge l k p)
  change (cocartesianStrictTransportEnrichedDiagram A).realization.app _
    (coherentNerveEdge (cocartesianBaseChangeNativeObjectIso l k p).hom).edge = _ at h
  have hr := congrArg (fun F ↦ F.app (Opposite.op ⦋1⦌)
    (coherentNerveEdge (cocartesianBaseChangeNativeObjectIso l k p).hom).edge)
      (cocartesianStrictTransportEnrichedDiagram_realization A)
  exact hr.symm.trans h

end SerrePositivity.InfinityCategories
