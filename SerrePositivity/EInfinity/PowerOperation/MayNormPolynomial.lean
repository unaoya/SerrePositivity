module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.GeomSum

/-!
# May の加法性に使う巡回ノルムの多項式

May, Proposition 2.3(ii) の T^{p−1}=N の係数恒等式。
F_p[X] で (X−1)^{p−1}=1+X+⋯+X^{p−1} を示す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.PowerOperation
open Polynomial
variable (p : ℕ) [Fact p.Prime]

/-- May の巡回境界に使う、標数 p の指定多項式の等式。 -/
lemma mayNormPolynomial :
    (X - 1 : Polynomial (ZMod p)) ^ (p - 1) =
      ∑ i ∈ Finset.range p, (X : Polynomial (ZMod p)) ^ i := by
  have hx : (X - 1 : Polynomial (ZMod p)) ≠ 0 := by
    intro h
    have hh := congrArg (fun f : Polynomial (ZMod p) => f.coeff 1) h
    simp [coeff_one] at hh
  apply mul_right_cancel₀ hx
  calc
    (X - 1 : Polynomial (ZMod p)) ^ (p - 1) * (X - 1) = (X - 1) ^ p := by
      rw [← pow_succ]
      congr 1
      exact Nat.sub_add_cancel (Fact.out : p.Prime).one_le
    _ = X ^ p - 1 := by rw [sub_pow_char, one_pow]
    _ = (∑ i ∈ Finset.range p, (X : Polynomial (ZMod p)) ^ i) * (X - 1) :=
      (geom_sum_mul X p).symm

/-- 同じ係数恒等式は、非可換な F_p 代数の任意の元にも評価できる。 -/
lemma mayNormPolynomial_aeval {A : Type*} [Ring A] [Algebra (ZMod p) A] (t : A) :
    (t - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, t ^ i := by
  have h := congrArg (Polynomial.aeval t) (mayNormPolynomial p)
  simpa only [map_pow, map_sub, map_one, map_sum, aeval_X] using h

end SerrePositivity.EInfinity.PowerOperation
