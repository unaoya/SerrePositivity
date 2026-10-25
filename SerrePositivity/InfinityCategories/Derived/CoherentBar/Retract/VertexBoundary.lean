module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundaryFaceTerms
/-!
概要：単体次数零では最初の正規化境界の列が零である。
方針：退化辺の唯一の面と単位 prefix を相殺し、元の頂点の列が零であることを使う。
規約：零単体の場合を高次元の式への不正な減算で扱わない。
使われ方：実正規化段階と普遍ラベル作用の比較の基底。
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
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarColumn_degenerate_vertex_zero (s : I _⦋0⦌) :
    dgCoherentBarColumn R D F (dgCoherentBarDegeneracy s 0) = 0 := by
  change (∑ i : Fin 1, ((0 : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
      dgCoherentBarFaceColumn R D F (I.σ 0 s) i) +
    (1 : ℤ).negOnePow •
      ∑ k : Fin 1, dgCoherentBarPrefixColumn R D F (I.σ 0 s) k.val (by omega) = 0
  simp only [Fin.sum_univ_one]
  change (2 : ℤ).negOnePow • dgCoherentBarFaceColumn R D F (I.σ 0 s) 0 +
    (1 : ℤ).negOnePow • dgCoherentBarPrefixColumn R D F (I.σ 0 s) 0 (by omega) = 0
  rw [dgCoherentBarPrefixColumn_first_degenerate_eq_face R D F s,
    Int.negOnePow_even 2 ⟨1, rfl⟩, Int.negOnePow_one]
  simp only [Units.neg_smul, one_smul, add_neg_cancel]

lemma dgCoherentBarNormalizationBoundary_restrict_vertex_zero (s : I _⦋0⦌) :
    (eHomWhiskerRight (Complex R)
      (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)
      (dgCoherentBarGraded R D F)).f 0
      (dgCoherentBarNormalizationBoundaryGraded R D F 0) = 0 := by
  have hl := dgCoherentBarTheta_comp_homotopyColumn R D F s 0 le_rfl
  have hi : (⟨0 - 0, by omega⟩ : Fin 1) = 0 := rfl
  rw [hi] at hl
  rw [dgCoherentBarColumn_degenerate_vertex_zero R D F s,
    DGNerve.zero_compose, smul_zero] at hl
  have h := dgCoherentBarNormalizationBoundaryGraded_restrict R D F 0 ⟨0, s⟩
  rw [hl] at h
  simp only [dgCoherentBarColumn, DGNerve.compose_zero, add_zero] at h
  exact h

end SerrePositivity.InfinityCategories
