module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.PositiveDegenerateFaceSum
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegeneratePrefixCoefficients
/-!
概要：正の退化位置の元の theta 列は、非退化因子への射影で消える。
方針：同じ面和の相殺と、退化 tail または退化高次 prefix の係数消滅を合わせる。
規約：元の dgCoherentBarColumn を使い、MC 仮定や模型の変更を加えない。
使われ方：実 bar の退化部分の保存と正規化商の構成。
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

set_option maxHeartbeats 800000 in
-- 同じ二つの直和の全 Hom end に有限面和と prefix 和を送るための局所上限。
lemma dgCoherentBarColumn_positive_degenerate_normalizedProjection {n : ℕ}
    (s : I _⦋n⦌) (j : Fin (n + 1)) (hj : 0 < j.val) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩)
      (dgCoherentBarNormalizedProjection R D F)).f 1
      (dgCoherentBarColumn R D F ⟨n + 1, I.σ j s⟩) = 0 := by
  have hface := dgCoherentBarPositiveDegenerateFaceSum_normalizedProjection R D F s j hj
  have hpre (k : Fin (n + 1)) :=
    dgCoherentBarPrefixColumn_degenerate_normalizedProjection R D F s j k.val
      (by omega) (Or.inl (by omega : j.val ≠ 0))
  simp only [Units.smul_def] at hface
  simp only [dgCoherentBarColumn, map_add, Units.smul_def, map_zsmul, map_sum]
  rw [hface]
  simp only [hpre, Finset.sum_const_zero, smul_zero, zero_add]

end SerrePositivity.InfinityCategories
