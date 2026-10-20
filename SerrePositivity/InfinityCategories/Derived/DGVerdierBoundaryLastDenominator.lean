module
public import SerrePositivity.InfinityCategories.Derived.RoofPointBoundaryHorn
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralFinalSimplex
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverVertexInverse

/-! # 任意次元の実分母 over 境界からの最後辺の分母性

概要：境界から作る一般最後ホーンの回収閉辺は、元の同じ境界頂点の実分母である。
方針：ホーンの実最後辺の join 表示と、回収閉射の実辺の厳密一致を使う。
規約：全次数、実分母部分圏の境界を入力。使われ方：一般同時残差消去の前提供給。
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

/-- 実分母部分圏内の境界から作る一般最後ホーン。 -/
def dgVerdierBoundaryHorn (P : Set D) (x : D) {n : ℕ}
    (B : (∂Δ[n + 1] : SSet.{max u v}) ⟶ (dgVerdierOver A D P x : SSet)) :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D :=
  roofPointBoundaryHorn ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
    (B ≫ (dgVerdierOver A D P x).ι)

/-- 回収した最後閉射の実辺は、同じ終端境界頂点の実分母である。 -/
lemma dgVerdierBoundaryLastClosed_mem (P : Set D) (x : D) {n : ℕ}
    (B : (∂Δ[n + 1] : SSet.{max u v}) ⟶ (dgVerdierOver A D P x : SSet)) :
    (dgClosedEdge A D (dgGeneralLastHornFinalClosed (dgVerdierBoundaryHorn A D P x B))).edge ∈
      dgVerdierEdges A D P := by
  rw [dgGeneralLastHornFinalClosed_edge]
  unfold dgVerdierBoundaryHorn
  rw [roofPointBoundaryHorn_lastEdge]
  change (roofPointSliceVertexEdge _ (SSet.yonedaEquiv
    (boundaryVertex n (Fin.last (n + 1)) ≫ (B ≫ (dgVerdierOver A D P x).ι)))).edge ∈ _
  rw [SSet.yonedaEquiv_comp]
  exact dgVerdierOverVertex_mem A D P x
    (B.app _ (SSet.yonedaEquiv (boundaryVertex n (Fin.last (n + 1)))))

end SerrePositivity.InfinityCategories
