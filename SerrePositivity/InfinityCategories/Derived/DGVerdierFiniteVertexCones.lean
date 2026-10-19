module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverTriangleEdge
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverVertexInverse
public import SerrePositivity.InfinityCategories.Derived.DGFiniteVerdierDenominators

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 有限実分母頂点へ、一つの閉分母から元の始域にも分母である実 over 辺を同時に供給する。 -/
theorem dgVerdierOverFinite_exists_commonSource (P : Set D) (x : D) {n : ℕ}
    (σ : Fin n → (dgVerdierOver A D P x : SSet.{max u v}) _⦋0⦌) :
    ∃ s : DGClosedVerdierDenominators A D P x,
      ∃ e : ∀ i, Truncated.Edge (X := (truncation 2).obj
        (dgVerdierOver A D P x : SSet.{max u v}))
        (dgClosedVerdierDenominatorVertex A D P x s) (σ i),
        ∀ i, (dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) (e i).edge ∈
          dgVerdierEdges A D P := by
  let a := (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)
  let y i := dgOverVertexSource A D x (σ i).val
  let S i := dgOverVertexEdge A D x (σ i).val
  have hS : ∀ i, (S i).edge ∈ dgVerdierEdges A D P := fun i =>
    dgVerdierOverVertex_mem A D P x (σ i)
  obtain ⟨q, T, hT, r, hr⟩ := dgVerdierEdges_commonDenominator A D P y S hS
  have hclosed : (dgClosedEdge A D (edgeClosed T)).edge = T.edge :=
    congrArg (fun e => e.edge) (dgClosedEdge_edgeClosed A D T)
  let s : DGClosedVerdierDenominators A D P x :=
    ⟨Over.mk (edgeClosed T), by
      change (dgClosedEdge A D (edgeClosed T)).edge ∈ dgVerdierEdges A D P
      exact hclosed.symm ▸ hT⟩
  let d := dgClosedVerdierDenominatorVertex A D P x s
  have hd : (dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) d = Simplex.vertex q :=
    dgClosedOverVertex_projection A D (edgeClosed T)
  have hdiag : (roofPointSliceVertexEdge a d.val).edge = T.edge :=
    (dgClosedOverVertex_edge A D (edgeClosed T)).trans hclosed
  have hex : ∀ i, ∃ e : Truncated.Edge (X := (truncation 2).obj
      (dgVerdierOver A D P x : SSet.{max u v})) d (σ i),
      (dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) e.edge ∈
        dgVerdierEdges A D P := by
    intro i
    have hσ : (dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) (σ i) =
        Simplex.vertex (y i) := by
      apply (dgNerve.vertexEquiv A D).injective
      rfl
    let R : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
        ((dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) d)
        ((dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) (σ i)) := {
      edge := (r i).edge
      src_eq := (r i).src_eq.trans hd.symm
      tgt_eq := (r i).tgt_eq.trans hσ.symm }
    let H := Classical.choice (hr i).2
    let H' : Truncated.Edge.CompStruct R (roofPointSliceVertexEdge a (σ i).val)
        (roofPointSliceVertexEdge a d.val) := {
      simplex := H.simplex
      d₂ := H.d₂
      d₀ := H.d₀
      d₁ := H.d₁.trans hdiag.symm }
    obtain ⟨e, he⟩ := dgVerdierOver_exists_edgeOfCompStruct A D P x d (σ i) R H'
    exact ⟨e, he.symm ▸ (hr i).1⟩
  choose e he using hex
  exact ⟨s, e, he⟩

end SerrePositivity.InfinityCategories
