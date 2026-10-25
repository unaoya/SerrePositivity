module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackThickClosure
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientThickKernelSource
public import SerrePositivity.InfinityCategories.Stable.StableClosureFullyFaithful
/-!
概要：同じ cell 平坦源の thick 核の対象は元の通常 pullback に属する。
方針：増大の完全充満忠実性で安定閉包を送り、公開された native retract 判定を適用する。
規約：同じ増大・元の対象条件と同じ平坦源を保持する。
使われ方：D-16 の実小核の本質像を元の充満 dg 包含へ同定する。
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
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackProperty_of_flatThick
    (x : DGCategoryCellResolution.Source R (DGGluingObject R C D M))
    (hx : dgThickClosureProperty R (DGCategoryCellResolution.Source R (DGGluingObject R C D M))
      (resolvedDGNullObjects R (DGGluingObject R C D M) (dgGluingPullbackProperty R C D M)) x) :
    dgGluingPullbackProperty R C D M
      ((DGCategoryCellResolution.augmentation R (DGGluingObject R C D M)).obj x) := by
  let := dgGluing_isDGPretriangulated R C D M hC hD
  let := dgCellResolutionSource_isDGPretriangulated R (DGGluingObject R C D M)
  let := dgNerve_isStable_of_pretriangulated R (DGGluingObject R C D M)
  let := dgNerve_isStable_of_pretriangulated R
    (DGCategoryCellResolution.Source R (DGGluingObject R C D M))
  let A := dgNerve.map (DGCategoryCellResolution.augmentation R (DGGluingObject R C D M))
  have hA := dgCellAugmentationNerve_isQCatEquivalence R (DGGluingObject R C D M)
  let := isExactFunctor_of_isQCatEquivalence hA
  have he : A.app (Opposite.op ⦋0⦌) ''
      (Simplex.vertex '' resolvedDGNullObjects R (DGGluingObject R C D M)
        (dgGluingPullbackProperty R C D M)) =
      Simplex.vertex '' dgGluingPullbackProperty R C D M := by
    ext b
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨_, hy, (dgFunctorNerve_vertex _ y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Simplex.vertex ⟨y⟩, ⟨⟨y⟩, hy, rfl⟩, ?_⟩
      exact dgFunctorNerve_vertex _ _
  obtain ⟨y, hy, ⟨r⟩⟩ :=
    (dgThickClosureProperty_iff_nativeStableRetract R _ _ x).mp hx
  have hy' := (stableVertexClosure_image_iff A hA.isFullyFaithful _ _).mpr hy
  rw [he] at hy'
  change StableVertexClosure _ (A.app _ (Simplex.vertex y)) at hy'
  dsimp only [A] at hy'
  rw [dgFunctorNerve_vertex] at hy'
  have hp := (dgGluingPullbackProperty_stableClosure_iff R C D M hC hD _).mp hy'
  apply dgGluingPullbackProperty_of_retract R C D M hC hD _ _ _ hp
  have rr := r.map (hoFunctor.map A).toFunctor
  change Retract ((SSet.mapHomotopyCategory A).obj _)
    ((SSet.mapHomotopyCategory A).obj _) at rr
  rw [SSet.mapHomotopyCategory_obj_mk, SSet.mapHomotopyCategory_obj_mk] at rr
  dsimp only [A] at rr
  rw [dgFunctorNerve_vertex, dgFunctorNerve_vertex] at rr
  exact Classical.choice ((homotopyRetract_ulift_iff _ _).mpr ⟨rr⟩)
end SerrePositivity.InfinityCategories
