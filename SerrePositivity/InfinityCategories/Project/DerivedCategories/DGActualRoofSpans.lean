module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofPointSliceEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictRoofQuotientVertex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierOverVertexInverse

/-! # 実屋根頂点と指定端点の実辺の span

概要：実屋根頂点を分母・分子の実辺として回収し、同じ実頂点へ戻す。
方針：実 slice の辺の相互表示と pullback 条件を使う。
規約：閉零射や元の対象の別表示を選ばない。使われ方：実合成屋根を元の実全空間に戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 指定 dg 対象の間の、実辺として表示した Verdier 屋根。 -/
abbrev DGActualRoofSpan (P : Set D) (x y : D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)

/-- 実辺 span の分母を、元の実分母 over 圏の頂点として表示する。 -/
def dgActualRoofSpanDenominatorVertex (P : Set D) (x y : D)
    (r : DGActualRoofSpan A D P x y) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex r.denominator, by
    intro α
    rw [SimplexCategory.hom_zero_zero α]
    simp only [op_id, Functor.map_id_apply]
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex r.denominator)).edge ∈ _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_edge]
    exact r.denominator_mem⟩

/-- span の分母頂点の始域は、指定した実 apex そのもの。 -/
lemma dgActualRoofSpanDenominatorVertex_source (P : Set D) (x y : D)
    (r : DGActualRoofSpan A D P x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌)
      (dgActualRoofSpanDenominatorVertex A D P x y r) = r.apex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_source r.denominator

/-- 実辺 span から、同じ分母・分子を持つ実屋根の点図式を作る。 -/
def dgActualRoofSpanPoint (P : Set D) (x y : D) (r : DGActualRoofSpan A D P x y) :
    Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y :=
  pullback.lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex r.numerator))
    (SSet.yonedaEquiv.symm (dgActualRoofSpanDenominatorVertex A D P x y r)) (by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_source, dgActualRoofSpanDenominatorVertex_source])

/-- 実辺 span が指定する、元の実屋根全空間の頂点。 -/
def dgActualRoofSpanVertex (P : Set D) (x y : D) (r : DGActualRoofSpan A D P x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y) _⦋0⦌ :=
  SSet.yonedaEquiv (dgActualRoofSpanPoint A D P x y r)

/-- span の実屋根頂点の実分母は、元の指定分母の頂点。 -/
lemma dgActualRoofSpanVertex_projection (P : Set D) (x y : D)
    (r : DGActualRoofSpan A D P x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y).app (Opposite.op ⦋0⦌)
      (dgActualRoofSpanVertex A D P x y r) = dgActualRoofSpanDenominatorVertex A D P x y r := by
  rw [dgActualRoofSpanVertex, ← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv (_ ≫ pullback.snd _ _) = _
  rw [dgActualRoofSpanPoint, pullback.lift_snd, Equiv.apply_symm_apply]

/-- span の実屋根頂点の実分子は、元の指定分子の slice 頂点。 -/
lemma dgActualRoofSpanVertex_target (P : Set D) (x y : D)
    (r : DGActualRoofSpan A D P x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y).app (Opposite.op ⦋0⦌)
      (dgActualRoofSpanVertex A D P x y r) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex r.numerator := by
  rw [dgActualRoofSpanVertex, ← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv (_ ≫ pullback.fst _ _) = _
  rw [dgActualRoofSpanPoint, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 元の実屋根頂点から、同じ実 apex・分母・分子の辺を回収する。 -/
def dgActualRoofVertexSpan (P : Set D) (x y : D)
    (r : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y) _⦋0⦌) : DGActualRoofSpan A D P x y := by
  let d := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y).app (Opposite.op ⦋0⦌) r
  let n := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y).app (Opposite.op ⦋0⦌) r
  let de := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) d.val
  let ne := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) n
  refine { apex := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) d
           denominator := { edge := de.edge
                            src_eq := de.src_eq
                            tgt_eq := de.tgt_eq.trans (Equiv.apply_symm_apply _ _) }
           denominator_mem := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertex_mem A D P x d
           numerator := { edge := ne.edge
                          src_eq := ne.src_eq.trans ?_
                          tgt_eq := ne.tgt_eq.trans (Equiv.apply_symm_apply _ _) } }
  exact congrArg (fun F => F.app (Opposite.op ⦋0⦌) r)
    (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
      (g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x))

/-- 実屋根の回収 span から作った実頂点は、元の頂点そのもの。 -/
theorem dgActualRoofVertexSpan_rightInverse (P : Set D) (x y : D)
    (r : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y) _⦋0⦌) :
    dgActualRoofSpanVertex A D P x y (dgActualRoofVertexSpan A D P x y r) = r := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPullbackSimplex_ext
  · change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y).app (Opposite.op ⦋0⦌)
      (dgActualRoofSpanVertex A D P x y (dgActualRoofVertexSpan A D P x y r)) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y).app (Opposite.op ⦋0⦌) r
    rw [dgActualRoofSpanVertex_target A D P x y (dgActualRoofVertexSpan A D P x y r)]
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_edge]
    rfl
  · change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y).app (Opposite.op ⦋0⦌)
      (dgActualRoofSpanVertex A D P x y (dgActualRoofVertexSpan A D P x y r)) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y).app (Opposite.op ⦋0⦌) r
    rw [dgActualRoofSpanVertex_projection A D P x y (dgActualRoofVertexSpan A D P x y r)]
    apply Subtype.ext
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_edge (dgActualRoofVertexSpan A D P x y r).denominator

end SerrePositivity.InfinityCategories.Project.DerivedCategories
