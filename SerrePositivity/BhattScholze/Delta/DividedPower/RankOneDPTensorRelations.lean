module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPBaseChangeMap
public import Mathlib.Data.Nat.Choose.Sum

/-! # 任意係数への一元分冪テンソル族の関係式

p正則性・p局所性を仮定せず、既存分冪代数の基底変更の逆射に必要な式を証明する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 既存分冪代数のテンソル内の、b^n⊗γ_n(1)という実族。 -/
def rankOneDPTensorValue (n : ℕ) (b : B) : B ⊗[A] DividedPowerAlgebra A A :=
  (b ^ n) ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A)

/-- 具体的テンソル族の零次関係。 -/
theorem rankOneDPTensorValue_zero (b : B) : rankOneDPTensorValue (A := A) 0 b = 1 := by
  rw [rankOneDPTensorValue, pow_zero, DividedPowerAlgebra.dp_zero,
    ← Algebra.TensorProduct.one_def]

/-- 具体的テンソル族の全スカラー関係。 -/
theorem rankOneDPTensorValue_smul (n : ℕ) (r b : B) :
    rankOneDPTensorValue (A := A) n (r • b) = r ^ n • rankOneDPTensorValue (A := A) n b := by
  simp only [rankOneDPTensorValue, smul_eq_mul, mul_pow, TensorProduct.smul_tmul']

/-- 具体的テンソル族の同一元の全積関係。 -/
theorem rankOneDPTensorValue_mul (n m : ℕ) (b : B) :
    rankOneDPTensorValue (A := A) n b * rankOneDPTensorValue (A := A) m b =
      (n + m).choose n • rankOneDPTensorValue (A := A) (n + m) b := by
  rw [rankOneDPTensorValue, rankOneDPTensorValue, rankOneDPTensorValue,
    Algebra.TensorProduct.tmul_mul_tmul, ← pow_add, DividedPowerAlgebra.dp_mul,
    TensorProduct.tmul_smul]

/-- 二項展開による、具体的テンソル族の全加法関係。 -/
theorem rankOneDPTensorValue_add (n : ℕ) (b c : B) :
    rankOneDPTensorValue (A := A) n (b + c) =
      (Finset.antidiagonal n).sum (fun k ↦
        rankOneDPTensorValue (A := A) k.1 b * rankOneDPTensorValue (A := A) k.2 c) := by
  simp only [rankOneDPTensorValue]
  rw [(Commute.all b c).add_pow', TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro k hk
  have hn : k.1 + k.2 = n := Finset.mem_antidiagonal.mp hk
  rw [Algebra.TensorProduct.tmul_mul_tmul, DividedPowerAlgebra.dp_mul, hn,
    TensorProduct.tmul_smul]
  exact (TensorProduct.smul_tmul' (n.choose k.1) (b ^ k.1 * c ^ k.2)
    (DividedPowerAlgebra.dp A n (1 : A))).symm

end SerrePositivity.BhattScholze
