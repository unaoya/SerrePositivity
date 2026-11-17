module

public import SerrePositivity.AlgebraicGeometry.HomogeneousEvaluationScaling
public import SerrePositivity.AlgebraicGeometry.SegreCoordinateRing
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
概要：Segre 座標の一列への代入と、元の斉次関係式との照合。
方針：同じ列の分母を全変数に掛ける評価を、斉次評価の拡大則に渡す。
規約：平坦性を仮定しない。
使われ方：元の次数一表示から Segre 標準開への逆向きの写像。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B) (j : κ)

/-- 一列への代入は、斉次多項式において分母の次数乗を純テンソルとして与える。 -/
theorem segreCoordinateMap_column {d : ℕ} (p : MvPolynomial ι R) (hp : p.IsHomogeneous d) :
    segreCoordinateMap (R := R) a b (MvPolynomial.rename (fun k ↦ (k, j)) p) =
      ((b j) ^ d) ⊗ₜ[R] MvPolynomial.aeval (R := R) a p := by
  have hcomp : (segreCoordinateMap (R := R) a b).comp
      (MvPolynomial.rename (fun k ↦ (k, j))) =
      MvPolynomial.aeval (R := R) (fun k ↦ b j ⊗ₜ[R] a k) := by
    ext k
    simp
  have heval : MvPolynomial.aeval (R := R) (fun k ↦ b j ⊗ₜ[R] a k) p =
      (b j ⊗ₜ[R] (1 : A)) ^ d *
        MvPolynomial.aeval (R := R) (fun k ↦ (1 : B) ⊗ₜ[R] a k) p := by
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using
      homogeneous_aeval_mul (R := R) (fun k ↦ (1 : B) ⊗ₜ[R] a k)
        (b j ⊗ₜ[R] (1 : A)) p hp
  change ((segreCoordinateMap (R := R) a b).comp
    (MvPolynomial.rename (fun k ↦ (k, j)))) p = _
  rw [hcomp, heval]
  have hi := MvPolynomial.comp_aeval_apply (R := R) (f := a)
    (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A) p
  simp only [Algebra.TensorProduct.includeRight_apply] at hi
  rw [← hi]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- 元の斉次関係式は、Segre 座標の一列へ代入しても同じ商で消える。 -/
theorem segreCoordinateProjection_column_zero {d : ℕ} (p : MvPolynomial ι R)
    (hp : p.IsHomogeneous d) (hz : MvPolynomial.aeval (R := R) a p = 0) :
    segreCoordinateProjection (R := R) a b (MvPolynomial.rename (fun k ↦ (k, j)) p) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change segreCoordinateMap (R := R) a b (MvPolynomial.rename (fun k ↦ (k, j)) p) = 0
  rw [segreCoordinateMap_column a b j p hp, hz, TensorProduct.tmul_zero]

end SerrePositivity.AlgebraicGeometry
