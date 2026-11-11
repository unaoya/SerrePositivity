module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryFaceTerms
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarColumn_degenerate_vertex_zero (s : I _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracy s 0) = 0 := by
  change (∑ i : Fin 1, ((0 : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ 0 s) i) +
    (1 : ℤ).negOnePow •
      ∑ k : Fin 1, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F (I.σ 0 s) k.val (by omega) = 0
  simp only [Fin.sum_univ_one]
  change (2 : ℤ).negOnePow • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ 0 s) 0 +
    (1 : ℤ).negOnePow • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F (I.σ 0 s) 0 (by omega) = 0
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPrefixColumn_first_degenerate_eq_face R D F s,
    Int.negOnePow_even 2 ⟨1, rfl⟩, Int.negOnePow_one]
  simp only [Units.neg_smul, one_smul, add_neg_cancel]

lemma dgCoherentBarNormalizationBoundary_restrict_vertex_zero (s : I _⦋0⦌) :
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨0, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F 0) = 0 := by
  have hl := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarTheta_comp_homotopyColumn R D F s 0 le_rfl
  have hi : (⟨0 - 0, by omega⟩ : Fin 1) = 0 := rfl
  rw [hi] at hl
  rw [dgCoherentBarColumn_degenerate_vertex_zero R D F s,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, smul_zero] at hl
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded_restrict R D F 0 ⟨0, s⟩
  rw [hl] at h
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, add_zero] at h
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
