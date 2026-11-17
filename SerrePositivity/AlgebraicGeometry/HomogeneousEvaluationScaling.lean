module

public import SerrePositivity.AlgebraicGeometry.DegreeOneGradedEvaluation

/-!
概要：同じ元を全変数に掛けた斉次多項式の評価。
方針：単項式の指数の和を斉次次数と照合する。
規約：係数環と評価先の宇宙を分け、元の非零性は仮定しない。
使われ方：Segre 座標の列・行の評価で関係式を降ろす。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R C ι : Type*} [CommRing R] [CommRing C] [Algebra R C]

/-- 全変数を c 倍した次数 d の斉次多項式の評価は c^d 倍になる。 -/
theorem homogeneous_aeval_mul (x : ι → C) (c : C) {d : ℕ} (p : MvPolynomial ι R)
    (hp : p.IsHomogeneous d) :
    MvPolynomial.aeval (R := R) (fun i ↦ c * x i) p =
      c ^ d * MvPolynomial.aeval (R := R) x p := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support hs]
  ring

end SerrePositivity.AlgebraicGeometry
