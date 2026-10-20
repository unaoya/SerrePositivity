module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierClosedVertexLegs
public import SerrePositivity.InfinityCategories.Derived.DGVerdierTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementPositiveDegeneracies
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementTriangle
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementCongruence
public import SerrePositivity.InfinityCategories.Derived.RoofTetrahedronDegeneracy

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable {C : DGVerdierDiagramVertexCone A D P x f}
variable (R : DGVerdierClosedVertexRefinement A D C)
variable (C)

omit [Small.{u} D] [IsDGPretriangulated A D] in
/-- 元の頂点脚の終点退化の回収四面体は、固定脚三角形の正番号退化。 -/
lemma dgVerdierLegDegenerateTetrahedron (v : K _⦋0⦌) :
    SSet.yonedaEquiv (roofPointSliceTetrahedron _
      (((dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge).val)) =
      (dgNerve A D).σ 1 (dgVerdierDiagramLegTriangle A D C v) :=
  (congrArg (SSet.yonedaEquiv (X := dgNerve A D))
    (roofPointSliceTetrahedron_degeneracy_one _ (C.leg v).edge.val)).trans
      (stdSimplex.yonedaEquiv_σ_comp (roofPointSliceTriangle _ (C.leg v).edge.val) 1)

omit [Small.{u} D] [IsDGPretriangulated A D] in
/-- 元の標準退化辺錐の回収始対象は、共通閉分母の同じ始対象。 -/
lemma dgVerdierLegDegenerateTetrahedron_source (v : K _⦋0⦌) :
    (SSet.yonedaEquiv (roofPointSliceTetrahedron _
      (((dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge).val))).obj 0 =
      ForgetEnrichment.to (Complex A) C.denominator.obj.left :=
  (congrArg (fun t : Simplex A D 3 => t.obj 0)
    (dgVerdierLegDegenerateTetrahedron A D C v)).trans (dgVerdierDiagramLegTriangle_source A D C v)

variable {C}

/-- 元の頂点脚の標準終点退化の閉細分は、新しい固定脚の同じ標準退化。 -/
lemma DGVerdierClosedVertexRefinement.refine_degenerateLeg (v : K _⦋0⦌) :
    dgVerdierTwoSimplexInitialRefinement A D P x
      ((dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge) R.q
      (dgClosedTargetTransport A D R.s (dgVerdierLegDegenerateTetrahedron_source A D C v).symm)
      (dgClosedTargetTransport_mem A D P R.s
        (dgVerdierLegDegenerateTetrahedron_source A D C v).symm R.denominator) =
      (dgVerdierOver A D P x : SSet).σ 1
        ((DGVerdierClosedVertexRefinement.vertexCone A D R).leg v).edge := by
  let sL := dgClosedTargetTransport A D R.s (dgVerdierDiagramLegTriangle_source A D C v).symm
  let sT := dgClosedTargetTransport A D R.s
    (dgVerdierLegDegenerateTetrahedron_source A D C v).symm
  have hc := dgSimplexInitialRefinement_congr (dgVerdierLegDegenerateTetrahedron A D C v)
    R.q R.q sT sL ((dgClosedTargetTransport_edge A D R.s _).trans
      (dgClosedTargetTransport_edge A D R.s _).symm)
  have hp := dgSimplexInitialRefinement_degeneracy_positive A D
    (dgVerdierDiagramLegTriangle A D C v) R.q sL (1 : Fin 3) (by decide)
  simp only [dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at hp
  have ht := dgSimplexInitialRefinement_triangle A D (dgVerdierDiagramLegTriangle A D C v) R.q sL
  have hn : dgSimplexInitialRefinement A D (SSet.yonedaEquiv (roofPointSliceTetrahedron _
      (((dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge).val))) R.q sT =
      (dgNerve A D).σ 1 (DGVerdierClosedVertexRefinement.legTriangle A D R v) :=
    hc.trans (hp.symm.trans (congrArg ((dgNerve A D).σ (1 : Fin 3)) ht))
  apply Subtype.ext
  apply roofPointSliceTetrahedron_injective
    ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
  have hl := dgVerdierTwoSimplexInitialRefinement_tetrahedron A D P x
    ((dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge) R.q sT
    (dgClosedTargetTransport_mem A D P R.s
      (dgVerdierLegDegenerateTetrahedron_source A D C v).symm R.denominator)
  have hr : roofPointSliceTetrahedron _
      (((dgVerdierOver A D P x : SSet).σ 1
        ((DGVerdierClosedVertexRefinement.vertexCone A D R).leg v).edge).val) =
      (SSet.yonedaEquiv (X := dgNerve A D)).symm ((dgNerve A D).σ 1
        (DGVerdierClosedVertexRefinement.legTriangle A D R v)) :=
    (roofPointSliceTetrahedron_degeneracy_one _
      (DGVerdierClosedVertexRefinement.vertexLegSimplex A D R v)).trans
      ((congrArg (fun g => SSet.stdSimplex.σ (1 : Fin 3) ≫ g)
        (DGVerdierClosedVertexRefinement.vertexLegSimplex_triangle A D R v)).trans
          (stdSimplex.σ_comp_yonedaEquiv_symm _ _))
  exact hl.trans ((congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm hn).trans hr.symm)

end SerrePositivity.InfinityCategories
