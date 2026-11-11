module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryExpansion
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.FaceHomotopyAction
/-!
概要：最後の正規化段では元の列へのホモトピーは消え、退化側の単位面だけが prefix として残る。
方針：面・prefix の次数消滅と零位置での単位面比較を、実境界の展開へ渡す。
規約：段階が単体次数に一致する場合を正位置の場合と区別する。
使われ方：最後の境界を始点保存の面・退化作用だけで計算する。
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

lemma dgCoherentBarHomotopy_comp_column_last_zero {n : ℕ} (s : I _⦋n + 1⦌) :
    _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded R D F (n + 1))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F ⟨n + 1, s⟩) rfl = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarHomotopy_comp_column_expansion R D F s (n + 1)
  have hf : (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceRightTerm R D F s (n + 1) i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceRightTerm_zero R D F s (n + 1) (by omega) i, smul_zero]
  have hp := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPrefixRightSum_at_zero R D F s
  rw [hf, hp, smul_zero, add_zero] at h
  exact h

lemma dgCoherentBarPrefixLeftTerm_last_eq_faceLeft {n : ℕ} (s : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPrefixLeftTerm R D F s n 0 = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceLeftTerm R D F s n 0 := by
  let T (j : Fin (n + 1)) := _root_.SerrePositivity.DifferentialGraded.compose R
    (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracy s j)))
    (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ j s) 0)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock R D F s j) (show (-1 : ℤ) + 1 = 0 from rfl)
  have hi : (⟨n - n, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext (Nat.sub_self n)
  have ht := congrArg T hi
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPrefixLeftTerm_at_zero_eq_face R D F s).trans ht.symm

lemma dgCoherentBarNormalizationBoundary_restrict_last_parts {n : ℕ}
    (s : I _⦋n + 1⦌) :
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨n + 1, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F (n + 1)) =
    (((n + 1 : ℕ) : ℤ) + 1).negOnePow •
      ((∑ i : Fin (n + 2), (((n + 1 : ℕ) : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceLeftTerm R D F s (n + 1) i) +
      (((n + 1 : ℕ) : ℤ) + 1).negOnePow •
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceLeftTerm R D F s (n + 1) 0) := by
  have hp := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPrefixLeftSum_at_zero R D F s).trans
    (dgCoherentBarPrefixLeftTerm_last_eq_faceLeft R D F s)
  have hexp := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarColumn_degeneracy_comp_expansion R D F s (n + 1)
  have hpoly := congrArg (fun z =>
      (∑ i : Fin (n + 2), (((n + 1 : ℕ) : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceLeftTerm R D F s (n + 1) i) +
      (((n + 1 : ℕ) : ℤ) + 1).negOnePow • z) hp
  have hleft := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarTheta_comp_homotopyColumn R D F s (n + 1) le_rfl).trans
    (congrArg (fun z => (((n + 1 : ℕ) : ℤ) + 1).negOnePow • z) (hexp.trans hpoly))
  have h := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded_restrict R D F (n + 1) ⟨n + 1, s⟩).trans
    (congrArg₂ (· + ·) hleft (dgCoherentBarHomotopy_comp_column_last_zero R D F s))
  exact h.trans (add_zero _)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
