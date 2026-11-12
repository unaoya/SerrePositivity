module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierOverTriangleEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierOverVertexInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteVerdierDenominators

/-! # 有限実分母頂点族の共通始点と実 over の脚

概要：有限個の実 Verdier over 頂点へ、一つの元の閉分母から実際の辺族を構成する。
方針：元の有限共通分母の合成三角形を、指定二端点付きの実 over 辺へ戻す。
規約：有限図式の辺との高次整合性はまだ主張しない。使われ方：共通始錐の零次部分。
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

/-- 有限実分母頂点へ、一つの閉分母から元の始域にも分母である実 over 辺を同時に供給する。 -/
theorem dgVerdierOverFinite_exists_commonSource (P : Set D) (x : D) {n : ℕ}
    (σ : Fin n → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋0⦌) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x,
      ∃ e : ∀ i, Truncated.Edge (X := (truncation 2).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s) (σ i),
        ∀ i, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) (e i).edge ∈
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P := by
  let a := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  let y i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x (σ i).val
  let S i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexEdge A D x (σ i).val
  have hS : ∀ i, (S i).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P := fun i =>
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertex_mem A D P x (σ i)
  obtain ⟨q, T, hT, r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges_commonDenominator A D P y S hS
  have hclosed : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed T)).edge = T.edge :=
    congrArg (fun e => e.edge) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_edgeClosed A D T)
  let s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x :=
    ⟨Over.mk (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed T), by
      change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed T)).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
      exact hclosed.symm ▸ hT⟩
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s
  have hd : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) d = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_projection A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed T)
  have hdiag : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a d.val).edge = T.edge :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed T)).trans hclosed
  have hex : ∀ i, ∃ e : Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})) d (σ i),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) e.edge ∈
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P := by
    intro i
    have hσ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) (σ i) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (y i) := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D).injective
      rfl
    let R : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) d)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) (σ i)) := {
      edge := (r i).edge
      src_eq := (r i).src_eq.trans hd.symm
      tgt_eq := (r i).tgt_eq.trans hσ.symm }
    let H := Classical.choice (hr i).2
    let H' : Truncated.Edge.CompStruct R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a (σ i).val)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a d.val) := {
      simplex := H.simplex
      d₂ := H.d₂
      d₀ := H.d₀
      d₁ := H.d₁.trans hdiag.symm }
    obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver_exists_edgeOfCompStruct A D P x d (σ i) R H'
    exact ⟨e, he.symm ▸ (hr i).1⟩
  choose e he using hex
  exact ⟨s, e, he⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
