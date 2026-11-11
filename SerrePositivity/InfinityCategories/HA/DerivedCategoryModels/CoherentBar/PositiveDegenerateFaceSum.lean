module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateFaceCoefficients
/-!
概要：正の位置で退化した単体の面係数の正規化像は相殺する。
方針：二つの例外面だけを残し、同じ面ラベルの係数と隣り合う符号を照合する。
規約：元の有限面和と全 Hom の符号を保持する。退化位置零は単位 prefix と別に照合する。
使われ方：実 theta による退化部分の保存の正位置の場合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

set_option maxHeartbeats 800000 in
-- 全 Hom end と二つの直和の有限面和を同時に照合するための局所上限。
lemma dgCoherentBarPositiveDegenerateFaceSum_normalizedProjection {n : ℕ}
    (s : I _⦋n⦌) (j : Fin (n + 1)) (hj : 0 < j.val) :
    (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
      (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ j s) i)) = 0 := by
  classical
  let l : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  let c := fun i : Fin (n + 1) => ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow
  let a := fun i : Fin (n + 1) =>
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ j s) i)
  change ∑ i, c i • a i = 0
  have hlj : l ≠ j := by
    intro h
    have := congrArg Fin.val h
    dsimp [l] at this
    omega
  have hzero (i : Fin (n + 1)) (hil : i ≠ l) (hij : i ≠ j) : a i = 0 := by
    apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFaceColumn_degenerate_normalizedProjection R D F s j i
    · intro h
      apply hil
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [l]
      simp only [Fin.val_succ, Fin.val_castSucc] at this
      omega
    · exact fun h => hij (Fin.succ_injective _ h)
  have hsum : ∑ i, c i • a i = c l • a l + c j • a j := by
    have hsub := Finset.sum_subset (f := fun i => c i • a i)
      (show ({l, j} : Finset (Fin (n + 1))) ⊆ Finset.univ from fun _ _ => Finset.mem_univ _)
      (fun i _ hi => by
        have hi' : i ≠ l ∧ i ≠ j := by simpa only [Finset.mem_insert, Finset.mem_singleton,
          not_or] using hi
        rw [hzero i hi'.1 hi'.2, smul_zero])
    exact hsub.symm.trans (Finset.sum_pair hlj)
  have hsame : a l = a j := by
    apply congrArg (fun z =>
      (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f 1 z)
    apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFaceColumn_eq_of_label_eq R D F
    have hl : l.succ = j.castSucc := Fin.ext (by dsimp [l]; omega)
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace
    rw [I.δ_comp_σ_self'_apply hl s, I.δ_comp_σ_succ_apply]
  have hsign : c j = -c l := by
    have he : (n : ℤ) + 1 + (j.val : ℤ) + 1 =
        ((n : ℤ) + 1 + (l.val : ℤ) + 1) + 1 := by dsimp [l]; omega
    dsimp [c]
    rw [he, Int.negOnePow_add]
    simp
  rw [hsum, hsame, hsign]
  simp only [Units.smul_def, Units.val_neg, neg_zsmul, add_neg_cancel]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
