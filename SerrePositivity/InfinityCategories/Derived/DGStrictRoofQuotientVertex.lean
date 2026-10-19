module
public import SerrePositivity.InfinityCategories.Derived.DGStrictQuotientRoofEdges

/-! # 厳密屋根頂点と実商比較の一致

概要：元の閉屋根頂点の実商像を、同じ分母と包含像の閉分子の指定頂点と同定する。
方針：標的 slice の頂点を回収辺で比較し、pullback の二射影から頂点を比較する。
規約：全厳密屋根 nerve の比較同値は仮定しない。使われ方：相対充填の両端の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定閉分子の標的 slice の商像は、その閉分子の包含像の指定頂点。 -/
lemma dgQuotientTargetSliceMap_closedVertex (P : Set D) (y : D)
    {q : ClosedCategory A D} (f : q ⟶ ForgetEnrichment.of (Complex A) y) :
    (dgQuotientTargetSliceMap A D P y).app (Opposite.op ⦋0⦌)
      (dgClosedOverVertex A D f) =
      dgClosedOverVertex A (DGQuotient.QuotientObject D P)
        ((DGQuotient.inclusion A D P).onClosed.map f) := by
  apply roofPointSliceVertexEdge_injective
  change (roofPointSliceVertexEdge _
    ((eqToIso (congrArg sliceOver (dgQuotientNervePoint A D P y))).hom.app _
      ((sliceOverPostcomp _ (dgQuotientNerveProjection A D P)).app _
        (dgClosedOverVertex A D f)))).edge = _
  rw [roofSliceTransport_edge (dgQuotientNervePoint A D P y),
    roofPointSliceVertexEdge_postcomp]
  exact (congrArg ((dgQuotientNerveProjection A D P).app (Opposite.op ⦋1⦌))
    (dgClosedOverVertex_edge A D f)).trans
      ((dgClosedEdge_map A D (DGQuotient.inclusion A D P) f).trans
          (dgClosedOverVertex_edge A (DGQuotient.QuotientObject D P)
            ((DGQuotient.inclusion A D P).onClosed.map f)).symm)

/-- 単体の pullback の同じ次数の元は二射影で決まる。 -/
lemma roofPullbackSimplex_ext {X Y Z : SSet.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    {n : SimplexCategoryᵒᵖ} {a b : (pullback f g).obj n}
    (hf : (pullback.fst f g).app n a = (pullback.fst f g).app n b)
    (hg : (pullback.snd f g).app n a = (pullback.snd f g).app n b) : a = b := by
  apply (SSet.yonedaEquiv (X := pullback f g)).symm.injective
  apply pullback.hom_ext
  · apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hf
  · apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hg

/-- 元の指定厳密屋根頂点の実商像は、指定された商分子の実屋根頂点。 -/
lemma dgRoofCorrespondenceMap_strictVertex (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x)
    (f : s.obj.left ⟶ ForgetEnrichment.of (Complex A) y) :
    (dgRoofCorrespondenceMap A D P x y).app (Opposite.op ⦋0⦌)
      (dgStrictRoofVertex A D P x y s f) =
      dgStrictQuotientRoofVertex A D P x y s
        ((DGQuotient.inclusion A D P).onClosed.map f) := by
  apply roofPullbackSimplex_ext
  · have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (dgStrictRoofVertex A D P x y s f)) (dgRoofCorrespondenceMap_target A D P x y)
    exact h.trans ((congrArg ((dgQuotientTargetSliceMap A D P y).app (Opposite.op ⦋0⦌))
      (dgStrictRoofVertex_target A D P x y s f)).trans
        ((dgQuotientTargetSliceMap_closedVertex A D P y f).trans
          (dgStrictQuotientRoofVertex_target A D P x y s _).symm))
  · have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (dgStrictRoofVertex A D P x y s f)) (dgRoofCorrespondenceMap_projection A D P x y)
    exact h.trans ((dgStrictRoofVertex_projection A D P x y s f).trans
      (dgStrictQuotientRoofVertex_projection A D P x y s _).symm)

end SerrePositivity.InfinityCategories
