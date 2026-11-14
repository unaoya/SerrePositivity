module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.OrdinaryPullbackThickClosure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientThickKernelSource
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableClosureFullyFaithful
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackProperty_of_flatThick
    (x : DGCategoryCellResolution.Source R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
    (hx : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty R (DGCategoryCellResolution.Source R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M)) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M
      ((DGCategoryCellResolution.augmentation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).obj x) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M hC hD
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R
    (DGCategoryCellResolution.Source R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
  have hA := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellAugmentationNerve_isQCatEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence hA
  have he : A.app (Opposite.op ⦋0⦌) ''
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M := by
    ext b
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨_, hy, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ⟨y⟩, ⟨⟨y⟩, hy, rfl⟩, ?_⟩
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ _
  obtain ⟨y, hy, ⟨r⟩⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty_iff_nativeStableRetract R _ _ x).mp hx
  have hy' := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableVertexClosure_image_iff A hA.isFullyFaithful _ _).mpr hy
  rw [he] at hy'
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure _ (A.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) at hy'
  dsimp only [A] at hy'
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at hy'
  have hp := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty_stableClosure_iff R C D M hC hD _).mp hy'
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty_of_retract R C D M hC hD _ _ _ hp
  have rr := r.map (hoFunctor.map A).toFunctor
  change Retract ((SSet.mapHomotopyCategory A).obj _)
    ((SSet.mapHomotopyCategory A).obj _) at rr
  rw [SSet.mapHomotopyCategory_obj_mk, SSet.mapHomotopyCategory_obj_mk] at rr
  dsimp only [A] at rr
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at rr
  exact Classical.choice ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyRetract_ulift_iff _ _).mpr ⟨rr⟩)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
