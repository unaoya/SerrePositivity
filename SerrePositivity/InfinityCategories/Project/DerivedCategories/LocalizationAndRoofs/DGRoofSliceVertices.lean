module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGClosedVerdierRoofDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration

/-! # 厳密閉分母から dg nerve の実 over slice の頂点へ

概要：元の閉分母の実辺を、指定終点上の実 slice の頂点として表示する。
方針：二点の join と標準辺の同型で両端を照合し、実辺を厳密に回収する。
規約：ここでは頂点比較を構成する。nerve 全体の同値や cofinality は主張しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

/-- 点上の実 slice の頂点から、その点へ入る実辺を回収する。 -/
def roofPointSliceVertexEdge {X : SSet.{u}} (a : Δ[0] ⟶ X) (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj X)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a).app (Opposite.op ⦋0⦌) σ) (SSet.yonedaEquiv a) where
  edge := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ σ.val)
  src_eq := by
    change X.δ 1 (SSet.yonedaEquiv _) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  tgt_eq := by
    change X.δ 0 (SSet.yonedaEquiv _) = SSet.yonedaEquiv a
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr,
      Category.assoc, Iso.hom_inv_id_assoc, σ.property]

/-- 実 slice の頂点は、回収した実辺の一次単体で一意に決まる。 -/
lemma roofPointSliceVertexEdge_injective {X : SSet.{u}} (a : Δ[0] ⟶ X)
    {σ τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋0⦌}
    (h : (roofPointSliceVertexEdge a σ).edge = (roofPointSliceVertexEdge a τ).edge) : σ = τ := by
  apply Subtype.ext
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).mp
  exact SSet.yonedaEquiv.injective h

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 元の閉分母は、dg nerve の指定終点上の実 slice の頂点を与える。 -/
def dgClosedOverVertex {q x : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D} (s : q ⟶ x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) x)))) _⦋0⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).tgt_eq⟩

/-- 実 slice の頂点の始点は、元の閉分母の始域。 -/
lemma dgClosedOverVertex_projection {q x : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D} (s : q ⟶ x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) x)))).app (Opposite.op ⦋0⦌)
      (dgClosedOverVertex A D s) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) q) := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] Δ[0] ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl, stdSimplex.yonedaEquiv_δ_comp,
    Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).src_eq

/-- 作った実 slice 頂点の辺は、元の指定閉分母の実辺そのもの。 -/
lemma dgClosedOverVertex_edge {q x : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D} (s : q ⟶ x) :
    (roofPointSliceVertexEdge _ (dgClosedOverVertex A D s)).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge)) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
