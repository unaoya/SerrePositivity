module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierFiniteCommonApex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierVertexLegTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGTriangleSourceRefinementCongruence

/-! # 一つの追加閉分母で細分した各頂点脚の実三角形

概要：脚の実三角形を頂点ごとに固定し、各同時充填の指定二面が同じ三角形と一致する。
方針：元の脚三角形と同じ追加閉辺の厳密一致から、細分三角形全体の一致を得る。
規約：辺に依存しない同じ頂点脚三角形。使われ方：有限実図式の一つの共通頂点錐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable {C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f} {m : ℕ} {e : Fin m → K _⦋1⦌}
variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement A D C e)

/-- 各頂点の元の脚三角形を、同じ一つの追加実閉分母で細分する。 -/
def DGVerdierFiniteEdgeRefinement.legTriangle (v : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v) T.q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D T.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C v).symm)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 各同時充填の面 023 は、終頂点の同じ固定細分脚三角形。 -/
lemma DGVerdierFiniteEdgeRefinement.refinedFace1_legTriangle (i : Fin m) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C (e i))
      (T.refinements i).q (T.refinements i).s =
      DGVerdierFiniteEdgeRefinement.legTriangle A D T (K.δ 0 (e i)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_congr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramCanonicalFace1_leg A D C (e i))
    (T.refinements i).q T.q (T.refinements i).s _
    ((T.denominator_edge_eq i).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D T.s
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C (K.δ 0 (e i))).symm).symm)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 各同時充填の面 013 は、始頂点の同じ固定細分脚三角形。 -/
lemma DGVerdierFiniteEdgeRefinement.refinedFace2_legTriangle (i : Fin m) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace2 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C (e i))
      (T.refinements i).q (T.refinements i).s =
      DGVerdierFiniteEdgeRefinement.legTriangle A D T (K.δ 1 (e i)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_congr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramCanonicalFace2_leg A D C (e i))
    (T.refinements i).q T.q (T.refinements i).s _
    ((T.denominator_edge_eq i).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D T.s
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C (K.δ 1 (e i))).symm).symm)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 頂点ごとの同じ細分脚三角形は、元の指定終頂点の分母辺を零面に保つ。 -/
lemma DGVerdierFiniteEdgeRefinement.legTriangle_face0 (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 (DGVerdierFiniteEdgeRefinement.legTriangle A D T v) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (f.app _ v).val).edge :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_face0 _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_face0 A D C v)

/-- 各細分脚三角形の対角辺は、同じ一つの共通閉細分頂点の分母辺。 -/
lemma DGVerdierFiniteEdgeRefinement.legTriangle_face1 (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (DGVerdierFiniteEdgeRefinement.legTriangle A D T v) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) T.commonApex.val).edge := by
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexClosedDiagonal A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v)
  have hg : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D g).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D C.denominator.obj.hom).edge :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexClosedDiagonal_edge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v)).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_diagonal A D C v)
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_comp_of_edge_eq A D
    (x' := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) C.denominator.obj.left) (y' := x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D T.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C v).symm) T.s
    g C.denominator.obj.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D T.s _) hg
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_face1_comp A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v) T.q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D T.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C v).symm)).trans
      (hc.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D T.commonDenominator.obj.hom).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
