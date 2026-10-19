module
public import SerrePositivity.InfinityCategories.Derived.DGStrictRoofQuotientVertex

/-! # 実 mapped 屋根の頂点から閉分母・閉分子を回収する

概要：任意の実 mapped 屋根頂点を、指定閉実分母と閉分子の厳密屋根で表示する。
方針：分母の閉表示と pullback 条件から分子辺の端点を同定し、閉零射へ戻す。
規約：頂点上の表示であり高次 cofinality は未主張。使われ方：有限充填の入力の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable (F : DGFunctor A D E)

/-- 実 mapped 屋根の分母の元の閉表示。 -/
def dgMappedRoofVertexDenominator (P : Set D) (x : D) (y : E)
    (z : (dgMappedRoofCorrespondence A D E F P x y) _⦋0⦌) :
    DGClosedVerdierDenominators A D P x :=
  dgVerdierOverVertexClosed A D P x
    ((pullback.snd _ _ : dgMappedRoofCorrespondence A D E F P x y ⟶ _).app
      (Opposite.op ⦋0⦌) z)

/-- 分母の閉表示を始域に指定した、実 mapped 屋根の分子辺。 -/
def dgMappedRoofVertexNumeratorEdge (P : Set D) (x : D) (y : E)
    (z : (dgMappedRoofCorrespondence A D E F P x y) _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj (dgNerve A E))
      (Simplex.vertex (F.obj (ForgetEnrichment.to (Complex A)
        (dgMappedRoofVertexDenominator A D E F P x y z).obj.left))) (Simplex.vertex y) where
  edge := (roofPointSliceVertexEdge _
    ((dgMappedRoofCorrespondenceTarget A D E F P x y).app (Opposite.op ⦋0⦌) z)).edge
  src_eq := (roofPointSliceVertexEdge _
    ((dgMappedRoofCorrespondenceTarget A D E F P x y).app (Opposite.op ⦋0⦌) z)).src_eq.trans
      (by
        have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌) z)
          (pullback.condition (f := sliceOverProjection
            ((SSet.yonedaEquiv (X := dgNerve A E)).symm (Simplex.vertex y)))
              (g := dgVerdierOverSource A D P x ≫ dgNerve.map F))
        refine h.trans ?_
        apply (dgNerve.vertexEquiv A E).injective
        rfl)
  tgt_eq := (roofPointSliceVertexEdge _
    ((dgMappedRoofCorrespondenceTarget A D E F P x y).app (Opposite.op ⦋0⦌) z)).tgt_eq.trans
      (Equiv.apply_symm_apply _ _)

/-- 実 mapped 屋根の分母の閉表示と同じ始域の閉分子。 -/
def dgMappedRoofVertexNumerator (P : Set D) (x : D) (y : E)
    (z : (dgMappedRoofCorrespondence A D E F P x y) _⦋0⦌) :
    F.onClosed.obj (dgMappedRoofVertexDenominator A D E F P x y z).obj.left ⟶
      ForgetEnrichment.of (Complex A) y :=
  edgeClosed (dgMappedRoofVertexNumeratorEdge A D E F P x y z)

/-- 回収した閉分母・閉分子は、元の実 mapped 屋根頂点を厳密に復元する。 -/
lemma dgStrictMappedRoofVertex_rightInverse (P : Set D) (x : D) (y : E)
    (z : (dgMappedRoofCorrespondence A D E F P x y) _⦋0⦌) :
    dgStrictMappedRoofVertex A D E F P x y (dgMappedRoofVertexDenominator A D E F P x y z)
      (dgMappedRoofVertexNumerator A D E F P x y z) = z := by
  apply roofPullbackSimplex_ext
  · refine (dgStrictMappedRoofVertex_target A D E F P x y _ _).trans ?_
    apply roofPointSliceVertexEdge_injective
    exact (dgClosedOverVertex_edge A E _).trans
      (congrArg (fun e => e.edge)
        (dgClosedEdge_edgeClosed A E (dgMappedRoofVertexNumeratorEdge A D E F P x y z)))
  · exact (dgStrictMappedRoofVertex_projection A D E F P x y _ _).trans
      (dgVerdierOverVertexClosed_vertex A D P x _)

/-- 厳密 mapped 屋根の nerve 比較は頂点上で全射。 -/
lemma dgStrictMappedRoofNerveMap_vertex_surjective (P : Set D) (x : D) (y : E) :
    Function.Surjective
      ((dgStrictMappedRoofNerveMap A D E F P x y).app (Opposite.op ⦋0⦌)) := by
  intro z
  exact ⟨nerveVertex (dgStrictMappedRoofMk A D E F P x y
    (dgMappedRoofVertexDenominator A D E F P x y z)
    (dgMappedRoofVertexNumerator A D E F P x y z)),
      dgStrictMappedRoofVertex_rightInverse A D E F P x y z⟩

end SerrePositivity.InfinityCategories
