module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorResolvedQuotient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolvedDGQuotientThickKernelSource
/-!
概要：Milnor 対角像の平坦源上の thick 核を、元 gluing の thick 閉包へ運ぶ。
方針：同じ増大の完全充満忠実性で安定閉包を送り、実 h 圏 retract を写す。
規約：元対角像と同じ cell 平坦源を保持する。前三角性は D-18 の供給境界。
使われ方：cell 平坦商の零対象反映を元対角の本質像へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
  [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d)]
lemma dgGluingMilnorDiagonal_flatThick_image
    (x : _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R (DGOdotGluing R d))
    (hx : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty R (DGCategoryCellResolution.Source R (DGOdotGluing R d))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
        (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty R (DGOdotGluing R d)
      (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
      ((_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R (DGOdotGluing R d)).obj x) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (DGOdotGluing R d)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated R (DGOdotGluing R d)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated R
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R (DGOdotGluing R d))
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (DGOdotGluing R d))
  have hA := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellAugmentationNerve_isQCatEquivalence R (DGOdotGluing R d)
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence hA
  have he : A.app (Opposite.op ⦋0⦌) ''
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
        (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) '' dgQuotientImage R (dgOdotQuotientInput R d).diagonal := by
    ext b
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨_, hy, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) ⟨y⟩, ⟨⟨y⟩, hy, rfl⟩, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ _⟩
  obtain ⟨y, hy, ⟨r⟩⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty_iff_nativeStableRetract R _ _ x).mp hx
  have hy' := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableVertexClosure_image_iff A hA.isFullyFaithful _ _).mpr hy
  rw [he] at hy'
  dsimp only [A] at hy'
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at hy'
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty_iff_nativeStableRetract R _ _ _).mpr
  refine ⟨_, hy', ?_⟩
  have rr := r.map (hoFunctor.map A).toFunctor
  change Retract ((SSet.mapHomotopyCategory A).obj _)
    ((SSet.mapHomotopyCategory A).obj _) at rr
  rw [SSet.mapHomotopyCategory_obj_mk, SSet.mapHomotopyCategory_obj_mk] at rr
  dsimp only [A] at rr
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at rr
  exact ⟨rr⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
