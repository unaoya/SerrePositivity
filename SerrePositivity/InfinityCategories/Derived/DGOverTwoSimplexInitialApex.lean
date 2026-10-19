module
public import SerrePositivity.InfinityCategories.Derived.DGOverTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementDiagonal
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverVertexInverse
public import SerrePositivity.InfinityCategories.Derived.RoofTetrahedronInitialDiagonal

/-! # 実 over 二単体の閉始点細分の新 apex の合成分母表示

概要：任意の実 over 二単体の細分後の始頂点の構造辺を、同じ閉射の実合成で表す。
方針：回収四面体の対角辺公式を使い、元の始頂点の分母条件と合成閉性を接続する。
規約：元の P を保つ。使われ方：同じ細分辺錐の実分母 over への持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable (x : D)
variable (σ : (sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm
  (Simplex.vertex x))) _⦋2⦌) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
  (((SSet.yonedaEquiv (X := dgNerve A D)) (roofPointSliceTetrahedron _ σ)).obj 0))


/-- 元の over 二単体の始点対角実辺から回収する閉射。 -/
def dgOverTwoSimplexInitialClosed :=
  ((dgNerve A D).δ 1 ((dgNerve A D).δ 1
    (SSet.yonedaEquiv (roofPointSliceTetrahedron _ σ)))).edgeClosed 0 1 (by decide)

/-- 回収した元の対角閉射の実辺は、元の始頂点の構造辺。 -/
lemma dgOverTwoSimplexInitialClosed_edge :
    (dgClosedEdge A D (dgOverTwoSimplexInitialClosed A D x σ)).edge =
      (roofPointSliceVertexEdge _ ((sliceOver _).δ 1 ((sliceOver _).δ 1 σ))).edge :=
  (dgSimplexEdge_closed_normal A D ((dgNerve A D).δ 1 ((dgNerve A D).δ 1
    (SSet.yonedaEquiv (roofPointSliceTetrahedron _ σ))))).symm.trans
      (roofPointSliceTetrahedron_initialDiagonal _ σ)

/-- 細分後の始頂点の構造辺は、同じ追加閉射と元の対角閉射の合成。 -/
lemma dgOverTwoSimplexInitialRefinement_apex_edge :
    (roofPointSliceVertexEdge _ ((sliceOver _).δ 1 ((sliceOver _).δ 1
      (dgOverTwoSimplexInitialRefinement A D x σ q s)))).edge =
      (dgClosedEdge A D (s ≫ dgOverTwoSimplexInitialClosed A D x σ)).edge := by
  have hr := congrArg (SSet.yonedaEquiv (X := dgNerve A D))
    (dgOverTwoSimplexInitialRefinement_tetrahedron A D x σ q s)
  change SSet.yonedaEquiv (roofPointSliceTetrahedron _
    (dgOverTwoSimplexInitialRefinement A D x σ q s)) =
      SSet.yonedaEquiv ((SSet.yonedaEquiv (X := dgNerve A D)).symm
        (dgSimplexInitialRefinement A D (SSet.yonedaEquiv (roofPointSliceTetrahedron _ σ)) q s))
    at hr
  rw [Equiv.apply_symm_apply] at hr
  exact (roofPointSliceTetrahedron_initialDiagonal _
    (dgOverTwoSimplexInitialRefinement A D x σ q s)).symm.trans
      ((congrArg (fun t : Simplex A D 3 => (dgNerve A D).δ 1 ((dgNerve A D).δ 1 t)) hr).trans
        (dgTetrahedronInitialRefinement_initialDiagonal A D
          (SSet.yonedaEquiv (roofPointSliceTetrahedron _ σ)) q s))

variable [Small.{u} D] [IsDGPretriangulated A D]

/-- 元の始頂点と追加閉射が実分母なら、同じ細分後の始頂点も実分母。 -/
lemma dgOverTwoSimplexInitialRefinement_apex_mem (P : Set D)
    (hA : IsDGVerdierOverVertex A D P x ((sliceOver _).δ 1 ((sliceOver _).δ 1 σ)))
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P) :
    IsDGVerdierOverVertex A D P x ((sliceOver _).δ 1 ((sliceOver _).δ 1
      (dgOverTwoSimplexInitialRefinement A D x σ q s))) := by
  unfold IsDGVerdierOverVertex at hA ⊢
  rw [dgOverTwoSimplexInitialRefinement_apex_edge]
  apply dgClosedVerdierDenominator_comp A D P s (dgOverTwoSimplexInitialClosed A D x σ) hs
  rw [dgOverTwoSimplexInitialClosed_edge]
  exact hA

end SerrePositivity.InfinityCategories
