module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentSignedLayerFaces
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ShiftPostcomposition

/-!
概要：同じ次元層の符号つき面を、元の raw 一次列の後合成として比較する。
方針：全 Hom の後合成の結合則と整数線形性を使う。
規約：零番の面は元の一次 prefix 列を保持する。
使われ方：実一次列の有限交代和への分解。
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

lemma dgCoherentBarSignedLayerFace_zero {n : ℕ} (s : I _⦋n + 1⦌) :
    dgCoherentBarSignedLayerFace R D G s 0 =
      (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩)
        (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)).f 1
          (((n : ℤ) + 1).negOnePow • dgCoherentBarPrefixColumn R D G s 0 (by omega)) := by
  dsimp only [dgCoherentBarSignedLayerFace, Fin.cases_zero, dgCoherentBarPrefixColumn]
  rw [dgStrictPostcompose_comp]
  simp only [Units.smul_def, map_zsmul]

lemma dgCoherentBarSignedLayerFace_succ {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    dgCoherentBarSignedLayerFace R D G s i.succ =
      (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩)
        (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)).f 1
          (((n : ℤ) + 1).negOnePow • dgCoherentBarFaceColumn R D G s i) := by
  dsimp only [dgCoherentBarSignedLayerFace, Fin.cases_succ, dgCoherentBarFaceColumn]
  rw [dgStrictPostcompose_comp]
  simp only [Units.smul_def, map_zsmul]

def dgCoherentBarFirstLayerColumn {n : ℕ} (s : I _⦋n + 1⦌) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n))).X 1 :=
  (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩)
    (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)).f 1
      (dgCoherentBarFirstColumn R D G s)

lemma dgCoherentBarFirstLayerColumn_d {n : ℕ} (s : I _⦋n + 1⦌) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n))).d 1 2
        (dgCoherentBarFirstLayerColumn R D G s) = 0 := by
  rw [dgCoherentBarFirstLayerColumn]
  erw [dgStrictHom_postcompose_d R D, dgCoherentBarFirstColumn_d, map_zero]

lemma dgCoherentBarFirstLayerColumn_eq_sum {n : ℕ} (s : I _⦋n + 1⦌) :
    dgCoherentBarFirstLayerColumn R D G s =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • dgCoherentBarSignedLayerFace R D G s i := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    dgCoherentBarSignedLayerFace_zero, dgCoherentBarSignedLayerFace_succ]
  rw [dgCoherentBarFirstLayerColumn, dgCoherentBarFirstColumn, map_add, map_sum]
  apply Eq.trans (add_comm _ _)
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [dgCoherentBarFirstFaceSign]
  exact map_zsmul _ _ _

end SerrePositivity.InfinityCategories
