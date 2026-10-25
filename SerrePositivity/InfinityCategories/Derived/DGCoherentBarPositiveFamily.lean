module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarDifferential
/-!
概要：正次元の元の bar 列を、面と prefix の一つの有限族として表す。
方針：二つの Fin 型の和で、元の標的ラベル・斉次係数・符号を同時に保持する。
規約：これは同じ bar 列の表示であり、κ 模型や元の図式は変更しない。
使われ方：有限列の微分・二乗の展開を HA 方程式へ接続する。
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

abbrev dgCoherentBarPositiveIndex (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)

def dgCoherentBarPositiveTarget {n : ℕ} (s : I _⦋n + 1⦌) :
    dgCoherentBarPositiveIndex n → dgCoherentBarIndex I
  | .inl i => dgCoherentBarFace s i.succ
  | .inr k => dgCoherentBarTail s (k.val + 1) (by omega)

def dgCoherentBarPositiveSign (n : ℕ) : dgCoherentBarPositiveIndex n → ℤˣ
  | .inl i => ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow
  | .inr _ => ((n : ℤ) + 1).negOnePow

def dgCoherentBarPositiveCoefficient {n : ℕ} (s : I _⦋n + 1⦌) :
    (j : dgCoherentBarPositiveIndex n) →
      (moduleHom R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
        (ForgetEnrichment.to (Complex R)
          (dgCoherentBarFamily R D F (dgCoherentBarPositiveTarget s j)))).X 1
  | .inl i => dgCoherentBarFaceBlock R D F s i
  | .inr k => dgCoherentBarPrefixBlock R D F s k.val (by omega)

def dgCoherentBarPositiveColumn {n : ℕ} (s : I _⦋n + 1⦌) :
    dgCoherentBarPositiveIndex n →
      (moduleHom R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X 1
  | .inl i => dgCoherentBarFaceColumn R D F s i
  | .inr k => dgCoherentBarPrefixColumn R D F s k.val (by omega)

-- This endpoint comparison unfolds the dependent Hom motive only in this proof.
set_option maxHeartbeats 800000 in
lemma dgCoherentBarPositiveColumn_eq_coefficient {n : ℕ} (s : I _⦋n + 1⦌)
    (j : dgCoherentBarPositiveIndex n) :
    dgCoherentBarPositiveColumn R D F s j =
      (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩)
        (Sigma.ι (dgCoherentBarFamily R D F) (dgCoherentBarPositiveTarget s j))).f 1
        (dgCoherentBarPositiveCoefficient R D F s j) := by
  cases j <;> rfl

lemma dgCoherentBarColumn_positive {n : ℕ} (s : I _⦋n + 1⦌) :
    dgCoherentBarColumn R D F ⟨n + 1, s⟩ =
      ∑ j : dgCoherentBarPositiveIndex n, dgCoherentBarPositiveSign n j •
        dgCoherentBarPositiveColumn R D F s j := by
  rw [Fintype.sum_sum_type]
  change
    (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
      dgCoherentBarFaceColumn R D F s i) +
      ((n : ℤ) + 1).negOnePow • ∑ k : Fin (n + 1),
        dgCoherentBarPrefixColumn R D F s k.val (by omega) = _
  congr 1
  rw [Finset.smul_sum]
  rfl

lemma dgCoherentBarColumn_positive_coefficients {n : ℕ} (s : I _⦋n + 1⦌) :
    dgCoherentBarColumn R D F ⟨n + 1, s⟩ =
      ∑ j : dgCoherentBarPositiveIndex n, dgCoherentBarPositiveSign n j •
        (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩)
          (Sigma.ι (dgCoherentBarFamily R D F) (dgCoherentBarPositiveTarget s j))).f 1
          (dgCoherentBarPositiveCoefficient R D F s j) := by
  rw [dgCoherentBarColumn_positive]
  apply Finset.sum_congr rfl
  intro j _
  rw [dgCoherentBarPositiveColumn_eq_coefficient]

end SerrePositivity.InfinityCategories
