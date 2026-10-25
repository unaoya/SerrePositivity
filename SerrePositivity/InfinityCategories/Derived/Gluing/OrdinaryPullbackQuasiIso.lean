module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackObjects
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedReflectsQuasiIso
/-!
概要：通常 pullback の対象条件は元 augmentation の準同型性に一致する。
方針：同じ矢印族の頂点辺を元の閉 augmentation の実分解像へ照合し、D-15 を適用する。
規約：元の加群射と追加 ULift 宇宙を保持する。
使われ方：通常 pullback の dg 対象条件を内在的に判定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
lemma dgGluingPullbackProperty_iff_quasiIso (X : DGGluingObject R C D M) :
    dgGluingPullbackProperty R C D M X ↔
      moduleQuasiIso R C (dgGluingAugmentation R C D M X) := by
  unfold dgGluingPullbackProperty
  rw [dgGluingDerivedAugmentationArrowDiagram_vertex]
  unfold IsEquivalencePathVertex
  rw [intervalFunctorVertexEdge_functorVertex, dgGluingDerivedAugmentationArrowDiagram,
    Equiv.apply_symm_apply]
  have h := dgModuleResolutionInfinity_ulift_isInvertibleEdge_iff.{u, v, max (u + 1) v w}
    R C (dgGluingAugmentation R C D M X)
  exact (isInvertibleEdge_congr (by rfl)).trans h
end SerrePositivity.InfinityCategories
