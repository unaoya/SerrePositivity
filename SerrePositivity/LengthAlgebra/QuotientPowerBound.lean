module

public import SerrePositivity.CommutativeAlgebra.Length.QuotientPower
public import SerrePositivity.LengthAlgebra.GeometricDecay

/-! # 正規化長さの巡回商の冪フィルトレーション評価

通常の長さと同じ右完全列を使い、零因子を許したまま、生成元の積・冪による
正規化長さの上界を証明する。冪ねじれ条件は固定イデアルへの包含から供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.NormalizedLength
open scoped ENNReal
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 固定した関係式がJの冪を含めば、それに任意の関係式を加えた商も冪ねじれ。 -/
theorem isPowTorsion_quotient_sup (I : Ideal R) (n : ℕ) (hJI : J ^ n ≤ I)
    (H : Ideal R) : IsPowTorsion J (R ⧸ (I ⊔ H)) := by
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
    Ideal.annihilator_quotient]
  exact hJI.trans le_sup_left

/-- 一つの関係式を積に置き換えた商の正規化長さは、二つの商の長さの和以下。 -/
theorem len_quotient_sup_span_mul_le (I : Ideal R) (n : ℕ) (hJI : J ^ n ≤ I)
    (x y : R) :
    lam.len (R ⧸ (I ⊔ Ideal.span {x * y})) ≤
      lam.len (R ⧸ (I ⊔ Ideal.span {x})) + lam.len (R ⧸ (I ⊔ Ideal.span {y})) :=
  lam.len_le_add_of_exact (quotientSupSpanMulMap R I x y)
    (quotientSupSpanMulProjection R I x y) (quotientSupSpanMul_exact R I x y)
    (isPowTorsion_quotient_sup I n hJI _) (isPowTorsion_quotient_sup I n hJI _)
    (isPowTorsion_quotient_sup I n hJI _)

/-- 一つの関係式をk乗に置き換えた商の正規化長さは高々k倍。 -/
theorem len_quotient_sup_span_pow_le (I : Ideal R) (n : ℕ) (hJI : J ^ n ≤ I)
    (x : R) (k : ℕ) :
    lam.len (R ⧸ (I ⊔ Ideal.span {x ^ k})) ≤
      (k : ℝ≥0∞) * lam.len (R ⧸ (I ⊔ Ideal.span {x})) := by
  induction k with
  | zero =>
      rw [pow_zero, Ideal.span_singleton_one, sup_top_eq, Nat.cast_zero, zero_mul]
      exact le_of_eq (lam.len_eq_zero_of_subsingleton _)
  | succ k ih =>
      calc
        _ ≤ lam.len (R ⧸ (I ⊔ Ideal.span {x ^ k})) +
            lam.len (R ⧸ (I ⊔ Ideal.span {x})) := by
          rw [pow_succ]
          exact lam.len_quotient_sup_span_mul_le I n hJI (x ^ k) x
        _ ≤ _ := by
          simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
            add_le_add ih (le_refl (lam.len (R ⧸ (I ⊔ Ideal.span {x}))))

/-- xのk乗が既存の関係式に入るとき、xを追加した商のk倍で元の商を上から評価できる。 -/
theorem len_quotient_le_mul_of_pow_mem (I : Ideal R) (n : ℕ) (hJI : J ^ n ≤ I)
    (x : R) (k : ℕ) (hx : x ^ k ∈ I) :
    lam.len (R ⧸ I) ≤ (k : ℝ≥0∞) * lam.len (R ⧸ (I ⊔ Ideal.span {x})) := by
  have heq : I ⊔ Ideal.span {x ^ k} = I :=
    sup_eq_left.mpr ((I.span_singleton_le_iff_mem).mpr hx)
  rw [← lam.len_congr (R ⧸ (I ⊔ Ideal.span {x ^ k})) (R ⧸ I)
    (Ideal.quotientEquivAlgOfEq R heq).toLinearEquiv]
  exact lam.len_quotient_sup_span_pow_le I n hJI x k

end SerrePositivity.NormalizedLength
