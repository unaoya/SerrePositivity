module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofPointBoundaryHorn
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralFinalSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierOverVertexInverse

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 実分母部分圏内の境界から作る一般最後ホーン。 -/
def dgVerdierBoundaryHorn (P : Set D) (x : D) {n : ℕ}
    (B : (∂Δ[n + 1] : SSet.{max u v}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)) :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointBoundaryHorn ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
    (B ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι)

/-- 回収した最後閉射の実辺は、同じ終端境界頂点の実分母である。 -/
lemma dgVerdierBoundaryLastClosed_mem (P : Set D) (x : D) {n : ℕ}
    (B : (∂Δ[n + 1] : SSet.{max u v}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed (dgVerdierBoundaryHorn A D P x B))).edge ∈
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed_edge]
  unfold dgVerdierBoundaryHorn
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointBoundaryHorn_lastEdge]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ (SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ (B ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι)))).edge ∈ _
  rw [SSet.yonedaEquiv_comp]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertex_mem A D P x
    (B.app _ (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)))))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
