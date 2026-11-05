module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorResolvedQuotient
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientThickKernelSource
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
  [IsDGPretriangulated R (DGOdotGluing R d)]
lemma dgGluingMilnorDiagonal_flatThick_image
    (x : DGCategoryCellResolution.Source R (DGOdotGluing R d))
    (hx : dgThickClosureProperty R (DGCategoryCellResolution.Source R (DGOdotGluing R d))
      (resolvedDGNullObjects R (DGOdotGluing R d)
        (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)) x) :
    dgThickClosureProperty R (DGOdotGluing R d)
      (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
      ((DGCategoryCellResolution.augmentation R (DGOdotGluing R d)).obj x) := by
  let := dgCellResolutionSource_isDGPretriangulated R (DGOdotGluing R d)
  let := dgNerve_isStable_of_pretriangulated R (DGOdotGluing R d)
  let := dgNerve_isStable_of_pretriangulated R
    (DGCategoryCellResolution.Source R (DGOdotGluing R d))
  let A := dgNerve.map (DGCategoryCellResolution.augmentation R (DGOdotGluing R d))
  have hA := dgCellAugmentationNerve_isQCatEquivalence R (DGOdotGluing R d)
  let := isExactFunctor_of_isQCatEquivalence hA
  have he : A.app (Opposite.op ⦋0⦌) ''
      (Simplex.vertex (A := R) '' resolvedDGNullObjects R (DGOdotGluing R d)
        (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)) =
      Simplex.vertex (A := R) '' dgQuotientImage R (dgOdotQuotientInput R d).diagonal := by
    ext b
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨_, hy, (dgFunctorNerve_vertex _ y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Simplex.vertex (A := R) ⟨y⟩, ⟨⟨y⟩, hy, rfl⟩, dgFunctorNerve_vertex _ _⟩
  obtain ⟨y, hy, ⟨r⟩⟩ :=
    (dgThickClosureProperty_iff_nativeStableRetract R _ _ x).mp hx
  have hy' := (stableVertexClosure_image_iff A hA.isFullyFaithful _ _).mpr hy
  rw [he] at hy'
  dsimp only [A] at hy'
  rw [dgFunctorNerve_vertex] at hy'
  apply (dgThickClosureProperty_iff_nativeStableRetract R _ _ _).mpr
  refine ⟨_, hy', ?_⟩
  have rr := r.map (hoFunctor.map A).toFunctor
  change Retract ((SSet.mapHomotopyCategory A).obj _)
    ((SSet.mapHomotopyCategory A).obj _) at rr
  rw [SSet.mapHomotopyCategory_obj_mk, SSet.mapHomotopyCategory_obj_mk] at rr
  dsimp only [A] at rr
  rw [dgFunctorNerve_vertex, dgFunctorNerve_vertex] at rr
  exact ⟨rr⟩
end SerrePositivity.InfinityCategories
