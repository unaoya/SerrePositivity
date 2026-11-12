module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexLegs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementPositiveDegeneracies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementCongruence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTetrahedronDegeneracy

/-! # 固定頂点脚の標準退化を保つ閉始点細分

概要：元の脚の終点を繰り返す標準辺錐の閉細分は、新固定脚の同じ標準退化。
方針：over 回収の退化公式、一般細分の正番号退化可換性、固定脚三角形を接続する。
規約：実分母部分圏内の厳密等式。使われ方：恒等図式辺の標準錐選択の保存。
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
variable (C)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 元の頂点脚の終点退化の回収四面体は、固定脚三角形の正番号退化。 -/
lemma dgVerdierLegDegenerateTetrahedron (v : K _⦋0⦌) :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge).val)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).σ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v) :=
  (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_degeneracy_one _ (C.leg v).edge.val)).trans
      (stdSimplex.yonedaEquiv_σ_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ (C.leg v).edge.val) 1)

omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 元の標準退化辺錐の回収始対象は、共通閉分母の同じ始対象。 -/
lemma dgVerdierLegDegenerateTetrahedron_source (v : K _⦋0⦌) :
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge).val))).obj 0 =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) C.denominator.obj.left :=
  (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => t.obj 0)
    (dgVerdierLegDegenerateTetrahedron A D C v)).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C v)

variable {C}

/-- 元の頂点脚の標準終点退化の閉細分は、新しい固定脚の同じ標準退化。 -/
lemma DGVerdierClosedVertexRefinement.refine_degenerateLeg (v : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement A D P x
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge) R.q
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s (dgVerdierLegDegenerateTetrahedron_source A D C v).symm)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P R.s
        (dgVerdierLegDegenerateTetrahedron_source A D C v).symm R.denominator) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexCone A D R).leg v).edge := by
  let sL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C v).symm
  let sT := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s
    (dgVerdierLegDegenerateTetrahedron_source A D C v).symm
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr (dgVerdierLegDegenerateTetrahedron A D C v)
    R.q R.q sT sL ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D R.s _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D R.s _).symm)
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_degeneracy_positive A D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v) R.q sL (1 : Fin 3) (by decide)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at hp
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_triangle A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C v) R.q sL
  have hn : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge).val))) R.q sT =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).σ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.legTriangle A D R v) :=
    hc.trans (hp.symm.trans (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).σ (1 : Fin 3)) ht))
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_injective
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement_tetrahedron A D P x
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge) R.q sT
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P R.s
      (dgVerdierLegDegenerateTetrahedron_source A D C v).symm R.denominator)
  have hr : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexCone A D R).leg v).edge).val) =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).σ 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.legTriangle A D R v)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_degeneracy_one _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexLegSimplex A D R v)).trans
      ((congrArg (fun g => SSet.stdSimplex.σ (1 : Fin 3) ≫ g)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexLegSimplex_triangle A D R v)).trans
          (stdSimplex.σ_comp_yonedaEquiv_symm _ _))
  exact hl.trans ((congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm hn).trans hr.symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
