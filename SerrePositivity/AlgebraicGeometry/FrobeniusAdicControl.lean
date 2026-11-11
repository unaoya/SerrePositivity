module

public import SerrePositivity.AlgebraicGeometry.AdicSemilinearMap
public import Mathlib.Algebra.CharP.Frobenius

/-!
概要：Frobenius に関するイデアル冪の p 倍の制御と、半線形な完備化写像。
方針：Frobenius のイデアルの像を Iᵖ に入れ、半線形写像の連続性へ渡す。
規約：指数標数 p を使い、Frobenius 線形性を係数準同型として明示する。
使われ方：Čech の Frobenius 写像を完備化比較と両立させる際の I 進制御。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type*} [CommRing R] (I : Ideal R) (p : ℕ) [ExpChar R p]

/-- Frobenius による I の像は、通常のイデアル冪 Iᵖ に含まれる。 -/
theorem frobeniusIdeal_map_le_pow : I.map (frobenius R p) ≤ I ^ p := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  exact Ideal.pow_mem_pow hx p

/-- Frobenius による I の像は、I 自身にも含まれる。 -/
theorem frobeniusIdeal_map_le_self : I.map (frobenius R p) ≤ I := by
  apply (frobeniusIdeal_map_le_pow I p).trans
  simpa only [pow_one] using
    (Ideal.pow_le_pow_right (I := I) (Nat.succ_le_of_lt (expChar_pos R p)))

variable {H K : Type*} [AddCommGroup H] [Module R H] [AddCommGroup K] [Module R K]
variable (f : H →ₛₗ[frobenius R p] K)

/-- Frobenius 半線形写像は、Iⁿ 倍を I^(p*n) 倍に送る。 -/
theorem frobeniusSemilinear_ideal_power_control (n : ℕ) :
    I ^ n • (⊤ : Submodule R H) ≤ (I ^ (p * n) • (⊤ : Submodule R K)).comap f := by
  simpa only [← pow_mul] using
    adicSemilinear_smul_top_le_comap I (I ^ p) f (frobeniusIdeal_map_le_pow I p) n

/-- Frobenius 半線形写像が誘導する、I 進完備化の間の Frobenius 半線形写像。 -/
def frobeniusSemilinearCompletionMap :
    AdicCompletion I H →ₛₗ[frobenius R p] AdicCompletion I K :=
  adicSemilinearCompletionMap I I f
    (fun n ↦ adicSemilinear_smul_top_le_comap I I f (frobeniusIdeal_map_le_self I p) n)

/-- 基底環の実際の Frobenius を、Frobenius 半線形な加群写像として見る。 -/
def frobeniusScalarSemilinearMap : R →ₛₗ[frobenius R p] R where
  toFun := frobenius R p
  map_add' := map_add (frobenius R p)
  map_smul' r x := map_mul (frobenius R p) r x

end SerrePositivity.AlgebraicGeometry
