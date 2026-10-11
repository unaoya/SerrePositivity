module

public import SerrePositivity.CommutativeAlgebra.GradedSurjection
public import SerrePositivity.CommutativeAlgebra.PolynomialHilbertSeries

/-! # 非零同次関係が成長の次数を下げること

整域上の非零同次元の乗法は単射である。その像を消す次数適合全射の行き先は、
関係式による商より大きい成長をもたない。多項式環の Hilbert 級数と合わせると、
非零同次関係をもつ標準次数環の累積成長の次数は、変数の個数より小さい。

一般の係数環上の線形射にも使える形を先に示す。多項式環の係数体から係数制限して
長さを測る場合にも、次数成分の有限長性と Hilbert 級数の式を渡して適用できる。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HomogeneousRelationGrowth

open HilbertSerre Polynomial Filter

variable {R A T : Type u} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
variable [AddCommGroup T] [Module R T]

/-- 乗法による関係を消す次数適合全射は、変数の個数より小さい累積成長しかもたない。
Hilbert 級数の式は仮定として受け取るので、係数体からの係数制限にも使える。
単なる線形射の核はイデアルとは限らないため、関係の全ての倍数が消えることを明示する。 -/
theorem natDegree_le_of_relation
    (NS : ℕ → Submodule R A) (NT : ℕ → Submodule R T)
    [DirectSum.Decomposition NS] [DirectSum.Decomposition NT]
    (F : A →ₗ[R] T) (hF : Function.Surjective F)
    (hdegreeF : ∀ n, ∀ x ∈ NS n, F x ∈ NT n)
    (f : A) (hf : f ≠ 0) (d : ℕ)
    (hdegreef : ∀ n, ∀ x ∈ NS n, f * x ∈ NS (n + d))
    (hrelation : ∀ x : A, F (f * x) = 0)
    (hfinite : ∀ n, IsFiniteLength R (NS n)) (s : ℕ)
    (hseries : lengthSeries NS = (PowerSeries.invOneSubPow ℚ (s + 1)).val)
    (P : ℚ[X]) (hP : 0 < P.leadingCoeff)
    (hpoly : ∀ᶠ n : ℕ in atTop, cumulativeLength NT n = P.eval (n : ℚ)) :
    P.natDegree ≤ s := by
  let m : A →ₗ[R] A := LinearMap.mulLeft R f
  have hm : Function.Injective m := mul_right_injective₀ hf
  have hrel : m.range ≤ F.ker := by
    rintro _ ⟨x, rfl⟩
    exact hrelation x
  apply natDegree_le_of_cumulative_quotient_bound NS hfinite m d hdegreef hm s 1
    (by simpa using hseries) P hP
  filter_upwards [hpoly] with n hn
  rw [← hn]
  exact cumulativeLength_le_quotient_of_surjective NS NT F hdegreeF hfinite hF m.range hrel n

/-- 環準同型の場合には、核の一つの非零同次元だけで全ての倍数が消えることが従う。 -/
theorem natDegree_le_of_relation_algHom
    {B : Type u} [CommRing B] [Algebra R B]
    (NS : ℕ → Submodule R A) (NT : ℕ → Submodule R B)
    [DirectSum.Decomposition NS] [DirectSum.Decomposition NT]
    (F : A →ₐ[R] B) (hF : Function.Surjective F)
    (hdegreeF : ∀ n, ∀ x ∈ NS n, F x ∈ NT n)
    (f : A) (hf : f ≠ 0) (d : ℕ)
    (hdegreef : ∀ n, ∀ x ∈ NS n, f * x ∈ NS (n + d)) (hrelation : F f = 0)
    (hfinite : ∀ n, IsFiniteLength R (NS n)) (s : ℕ)
    (hseries : lengthSeries NS = (PowerSeries.invOneSubPow ℚ (s + 1)).val)
    (P : ℚ[X]) (hP : 0 < P.leadingCoeff)
    (hpoly : ∀ᶠ n : ℕ in atTop, cumulativeLength NT n = P.eval (n : ℚ)) :
    P.natDegree ≤ s := by
  exact natDegree_le_of_relation NS NT F.toLinearMap hF hdegreeF f hf d hdegreef
    (fun x ↦ by simp [map_mul, hrelation]) hfinite s hseries P hP hpoly

/-- 体上の多項式環の次数成分を用いた形。 -/
theorem natDegree_le_of_polynomial_relation
    (k : Type u) [Field k] {T : Type u} [AddCommGroup T] [Module k T]
    (s : ℕ) (NT : ℕ → Submodule k T) [DirectSum.Decomposition NT]
    (F : MvPolynomial (Fin (s + 1)) k →ₗ[k] T) (hF : Function.Surjective F)
    (hdegreeF : ∀ n, ∀ x ∈ MvPolynomial.homogeneousSubmodule (Fin (s + 1)) k n,
      F x ∈ NT n)
    (f : MvPolynomial (Fin (s + 1)) k) (hf : f ≠ 0) (d : ℕ)
    (hdegreef : f.IsHomogeneous d) (hrelation : ∀ x, F (f * x) = 0)
    (P : ℚ[X]) (hP : 0 < P.leadingCoeff)
    (hpoly : ∀ᶠ n : ℕ in atTop, cumulativeLength NT n = P.eval (n : ℚ)) :
    P.natDegree ≤ s := by
  let : DirectSum.Decomposition (MvPolynomial.homogeneousSubmodule (Fin (s + 1)) k) :=
    MvPolynomial.decomposition
  apply natDegree_le_of_relation (MvPolynomial.homogeneousSubmodule (Fin (s + 1)) k)
    NT F hF hdegreeF f hf d ?_ hrelation
    (PolynomialHilbertSeries.finiteLength_homogeneousSubmodule k (Fin (s + 1))) s
    (PolynomialHilbertSeries.lengthSeries_homogeneousSubmodule k (s + 1)) P hP hpoly
  intro n x hx
  simpa [Nat.add_comm] using hdegreef.mul hx

end SerrePositivity.HomogeneousRelationGrowth
