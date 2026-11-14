module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedEqualityTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierClosedVertexRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierVertexLegTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGTriangleSourceRefinementCongruence

/-! # 同じ閉分母で細分した頂点ごとの固定脚三角形

概要：元の頂点錐と追加実閉分母だけから、各頂点の同じ細分脚三角形を固定する。
方針：零面を保ち、対角辺を共通閉細分分母の実辺へ同定する。
規約：辺族に依存しない。使われ方：高次の各辺錐の二脚の共通化。
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
variable {C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement A D C)

/-- 各頂点の元の脚三角形を、同じ一つの追加実閉分母で細分する。 -/
def DGVerdierClosedVertexRefinement.legTriangle (v : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v) R.q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C v).symm)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 頂点ごとの同じ細分脚三角形は、元の指定終頂点の分母辺を零面に保つ。 -/
lemma DGVerdierClosedVertexRefinement.legTriangle_face0 (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 (DGVerdierClosedVertexRefinement.legTriangle A D R v) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (f.app _ v).val).edge :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_face0 _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_face0 A D C v)

/-- 各細分脚三角形の対角辺は、同じ一つの共通閉細分頂点の分母辺。 -/
lemma DGVerdierClosedVertexRefinement.legTriangle_face1 (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (DGVerdierClosedVertexRefinement.legTriangle A D R v) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) R.commonApex.val).edge := by
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexClosedDiagonal A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v)
  have hg : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D g).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D C.denominator.obj.hom).edge :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexClosedDiagonal_edge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v)).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_diagonal A D C v)
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_comp_of_edge_eq A D
    (x' := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) C.denominator.obj.left) (y' := x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C v).symm) R.s
    g C.denominator.obj.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D R.s _) hg
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_face1_comp A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v) R.q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C v).symm)).trans
      (hc.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D R.commonDenominator.obj.hom).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
