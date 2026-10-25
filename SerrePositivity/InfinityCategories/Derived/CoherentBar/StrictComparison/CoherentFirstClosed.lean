module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstDifferential
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarFaceDifferential
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarPrefixDifferential
public import SerrePositivity.InfinityCategories.DGNerve.CoherentDiagramEdgeBoundary

/-!
概要：一次成分の各列は元の内部微分について閉じている。
方針：面ブロックの閉性と、辺の HA 境界が零であることを使う。
規約：辺の鎖写像の strict な合成保存は要求しない。
使われ方：内部ホモロジーに誘導する一次成分の微分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixBoundary_zero {n : ℕ} (s : I _⦋n⦌) (h : 1 ≤ n) :
    dgCoherentBarPrefixBoundary R D G s 0 h = 0 := by
  unfold dgCoherentBarPrefixBoundary
  rw [coherentDiagramTopBoundary_edge, map_zero]

lemma dgCoherentBarPrefixBlock_zero_d {n : ℕ} (s : I _⦋n⦌) (h : 1 ≤ n) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D G (dgCoherentBarTail s 1 h)))).d 1 2
      (dgCoherentBarPrefixBlock R D G s 0 h) = 0 := by
  rw [dgCoherentBarPrefixBlock_d, dgCoherentBarPrefixBoundary_zero,
    moduleHomShiftBlock_zero, smul_zero]

lemma dgCoherentBarFaceColumn_d {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G))).d 1 2
      (dgCoherentBarFaceColumn R D G s i) = 0 := by
  unfold dgCoherentBarFaceColumn
  erw [dgStrictHom_postcompose_d R D, dgCoherentBarFaceBlock_d, map_zero]

lemma dgCoherentBarPrefixColumn_zero_d {n : ℕ} (s : I _⦋n⦌) (h : 1 ≤ n) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G))).d 1 2
      (dgCoherentBarPrefixColumn R D G s 0 h) = 0 := by
  unfold dgCoherentBarPrefixColumn
  erw [dgStrictHom_postcompose_d R D, dgCoherentBarPrefixBlock_zero_d, map_zero]

lemma dgCoherentBarFirstColumn_d {n : ℕ} (s : I _⦋n + 1⦌) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G))).d 1 2
      (dgCoherentBarFirstColumn R D G s) = 0 := by
  simp only [dgCoherentBarFirstColumn, map_add, map_sum, Units.smul_def, map_zsmul,
    dgCoherentBarFaceColumn_d, dgCoherentBarPrefixColumn_zero_d, zsmul_zero,
    Finset.sum_const_zero, add_zero]

end SerrePositivity.InfinityCategories
