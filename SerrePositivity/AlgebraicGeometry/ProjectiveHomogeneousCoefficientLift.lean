module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
概要：全射な係数変更に沿って、同じ次数の斉次多項式を持ち上げる。
方針：任意の多項式の持ち上げから、指定した次数成分だけを取る。
規約：斉次成分と係数変更の交換を係数ごとに示す。
使われ方：閉厚化の商係数多項式作用が Proj 次数を保つことに使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R B ι : Type*} [CommRing R] [CommRing B]
variable (f : R →+* B)

/-- 多項式の次数成分を取る操作は、任意の係数変更と交換する。 -/
theorem projectiveHomogeneousComponent_map (n : ℕ) (p : MvPolynomial ι R) :
    MvPolynomial.map f (MvPolynomial.homogeneousComponent n p) =
      MvPolynomial.homogeneousComponent n (MvPolynomial.map f p) := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp only [map_zero]

/-- 全射な係数変更では、斉次多項式を同じ次数のまま持ち上げられる。 -/
theorem projectiveHomogeneousCoefficientLift (hf : Function.Surjective f)
    {n : ℕ} (p : MvPolynomial ι B) (hp : p ∈ MvPolynomial.homogeneousSubmodule ι B n) :
    ∃ q : MvPolynomial ι R, q ∈ MvPolynomial.homogeneousSubmodule ι R n ∧
      MvPolynomial.map f q = p := by
  obtain ⟨q, hq⟩ := MvPolynomial.map_surjective f hf p
  refine ⟨MvPolynomial.homogeneousComponent n q,
    MvPolynomial.homogeneousComponent_mem n q, ?_⟩
  rw [projectiveHomogeneousComponent_map, hq]
  exact MvPolynomial.homogeneousComponent_eq_self hp

end SerrePositivity.AlgebraicGeometry
