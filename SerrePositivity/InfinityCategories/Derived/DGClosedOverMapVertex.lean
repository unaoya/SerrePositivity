module
public import SerrePositivity.InfinityCategories.Derived.OrdinaryRoofVertexEdge
public import SerrePositivity.InfinityCategories.Derived.DGClosedNerveOverMap

/-! # 閉 over nerve 比較の指定頂点

概要：厳密 over 比較の零単体は、指定閉構造射から直接作った実 slice 頂点に一致する。
方針：固定図式の輸送と後合成を外し、通常の over の構造射の計算へ戻す。
規約：対象と Hom の独立宇宙を保持する。使われ方：実分母全部分圏への因子化。
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

/-- 共通宇宙へ上げた閉構造射の nerve 辺を、元の閉圏へ戻す。 -/
lemma dgCommonClosedNerveDown_edge {q x : ClosedCategory A D} (s : q ⟶ x) :
    (dgCommonClosedNerveDown A D).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ ((AsSmall.up : ClosedCategory A D ⥤
        DGCommonClosedCategory A D).map s)) = ComposableArrows.mk₁ s := by
  refine ComposableArrows.ext₁ (F := _ ⋙ AsSmall.down)
    (G := ComposableArrows.mk₁ s) rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 厳密閉 over 比較から回収した実辺は元の指定構造射の実辺。 -/
lemma dgClosedNerveOverMap_edge (x : D)
    (s : Over (ForgetEnrichment.of (Complex A) x)) :
    (roofPointSliceVertexEdge _
      ((dgClosedNerveOverMap A D x).app (Opposite.op ⦋0⦌) (nerveVertex s))).edge =
        (dgClosedEdge A D s.hom).edge := by
  let c := (AsSmall.up : ClosedCategory A D ⥤ DGCommonClosedCategory A D).obj
    (ForgetEnrichment.of (Complex A) x)
  let t := (F1B.kanNerveOverIso c).hom.app (Opposite.op ⦋0⦌)
    (nerveVertex ((Over.post (AsSmall.up : ClosedCategory A D ⥤
      DGCommonClosedCategory A D)).obj s))
  change (roofPointSliceVertexEdge _
    ((eqToIso (congrArg sliceOver (dgCommonClosedNervePoint A D x))).hom.app _
      ((sliceOverPostcomp (nervePoint c) (dgCommonClosedNerveToDG A D)).app _ t))).edge = _
  rw [roofSliceTransport_edge (dgCommonClosedNervePoint A D x),
    roofPointSliceVertexEdge_postcomp]
  change (dgCommonClosedNerveToDG A D).app (Opposite.op ⦋1⦌)
    (roofPointSliceVertexEdge (nervePoint c) t).edge = _
  rw [ordinaryRoofVertexEdge]
  change (closedNerveInclusion A D).app (Opposite.op ⦋1⦌)
    ((dgCommonClosedNerveDown A D).app _ (ComposableArrows.mk₁
      ((AsSmall.up : ClosedCategory A D ⥤ DGCommonClosedCategory A D).map s.hom))) = _
  rw [dgCommonClosedNerveDown_edge]
  apply (dgNerve.edgeEquiv A D).injective
  rw [closedNerveInclusion_edge]
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    rfl

/-- 比較で得た実 slice 頂点は、元の閉構造射から作った頂点そのもの。 -/
lemma dgClosedNerveOverMap_vertex (x : D)
    (s : Over (ForgetEnrichment.of (Complex A) x)) :
    (dgClosedNerveOverMap A D x).app (Opposite.op ⦋0⦌) (nerveVertex s) =
      dgClosedOverVertex A D s.hom := by
  apply roofPointSliceVertexEdge_injective
  exact (dgClosedNerveOverMap_edge A D x s).trans
    (dgClosedOverVertex_edge A D s.hom).symm

end SerrePositivity.InfinityCategories
