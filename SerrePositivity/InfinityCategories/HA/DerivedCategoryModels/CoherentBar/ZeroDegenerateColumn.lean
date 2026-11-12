module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateUnitCoefficients
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegeneratePrefixCoefficients
/-!
概要：位置零の退化単体の元の theta 列は、非退化射影の後に零になる。
方針：最初の面と単位 prefix だけを残し、同じ係数の反対符号を相殺する。
規約：元の列・有限和・shift ブロックを保持する。MC 仮定はこの係数検証には不要。
使われ方：実 theta の退化部分の保存を全退化位置へ拡張する。
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
-- 同じ全 Hom end の面和と prefix 和を、二つの例外係数へ還元する局所上限。
lemma dgCoherentBarColumn_zero_degenerate_normalizedProjection {n : ℕ} (s : I _⦋n⦌) :
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, I.σ 0 s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F ⟨n + 1, I.σ 0 s⟩) = 0 := by
  classical
  let L := (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, I.σ 0 s⟩)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f 1
  have hf (i : Fin (n + 1)) (hi : i ≠ 0) :
      L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ 0 s) i) = 0 := by
    apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFaceColumn_degenerate_normalizedProjection R D F s 0 i
    · simp
    · exact fun h => hi (Fin.succ_injective _ h)
  have hp (i : Fin (n + 1)) (hi : i ≠ 0) :
      L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F (I.σ 0 s) i.val (by omega)) = 0 :=
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPrefixColumn_degenerate_normalizedProjection R D F s 0 i.val
      (by omega) (Or.inr (by intro h; apply hi; exact Fin.ext h))
  have hface : (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
      L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ 0 s) i)) =
      ((n : ℤ) + 1 + 0 + 1).negOnePow •
        L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ 0 s) 0) := by
    apply Finset.sum_eq_single (0 : Fin (n + 1))
    · intro i _ hi
      rw [hf i hi, smul_zero]
    · simp
  have hprefix : (∑ i : Fin (n + 1),
      L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F (I.σ 0 s) i.val (by omega))) =
      L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F (I.σ 0 s) 0 (by omega)) := by
    apply Finset.sum_eq_single (0 : Fin (n + 1))
    · intro i _ hi
      exact hp i hi
    · simp
  have hsign : ((n : ℤ) + 1 + 0 + 1).negOnePow = -((n : ℤ) + 1).negOnePow := by
    rw [add_zero, Int.negOnePow_add]
    simp
  change L _ = 0
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn, Units.smul_def, map_add, map_zsmul, map_sum]
  simp only [Units.smul_def] at hface
  rw [hface, hprefix, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPrefixColumn_first_degenerate_eq_face,
    hsign]
  simp only [Units.val_neg, neg_zsmul, neg_add_cancel]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
