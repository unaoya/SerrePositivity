module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Graded.HilbertSeries
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # 多項式環の Hilbert 級数と斉次関係の増大

## 概要

全次数 `n` の単項式の個数（`Sym σ n` との対応、重複組合せ）、多変数多項式環の斉次成分の基底と次元、
その Hilbert 級数 `(1 - X)^{-s}`、および斉次関係で割った商の累積長さが一段低い次数で抑えられることを示す。

## 方針

単項式は `Finsupp` の次数で数える。商の増大は、斉次関係の倍写像が次数付きの単射であることと
`Graded/HilbertSeries` の漸化式による。

## 規約

名前空間は `HilbertSerre`。

## 使われ方

正則局所環の随伴次数環の表示の単射性（`RegularLocalRing/Graded`）。
-/

@[expose] public noncomputable section

universe u v w

section Monomials

namespace SerrePositivity.HilbertSerre

/-- 単項式の指数の全次数は、対応する多重集合の濃度に等しい。 -/
theorem card_toMultiset_eq_degree {σ : Type*} (m : σ →₀ ℕ) :
    m.toMultiset.card = m.degree := by
  rw [Finsupp.card_toMultiset]
  rfl

/-- 多重集合を単項式の指数へ変換すると、全次数は元の濃度になる。 -/
theorem degree_toFinsupp_eq_card {σ : Type*} [DecidableEq σ] (s : Multiset σ) :
    s.toFinsupp.degree = s.card := by
  classical
  change s.toFinsupp.sum (fun _ ↦ id) = s.card
  exact Multiset.toFinsupp_sum_eq s

/-- 次数 `n` の単項式の指数と、`n` 個の変数からなる多重集合との全単射。 -/
def degreeEquivSym (σ : Type*) (n : ℕ) :
    {m : σ →₀ ℕ // m.degree = n} ≃ Sym σ n := by
  classical
  exact {
    toFun := fun m ↦ ⟨m.1.toMultiset, (card_toMultiset_eq_degree m.1).trans m.2⟩
    invFun := fun s ↦ ⟨(s : Multiset σ).toFinsupp,
      (degree_toFinsupp_eq_card (s : Multiset σ)).trans s.2⟩
    left_inv := fun m ↦ Subtype.ext (Finsupp.toMultiset_toFinsupp m.1)
    right_inv := fun s ↦ Sym.ext (Multiset.toFinsupp_toMultiset (s : Multiset σ)) }

/-- 有限個の変数について、次数 `n` の単項式の数は重複組合せである。
サブタイプの `Fintype` は任意のものを使える。 -/
theorem card_degree_eq_multichoose (σ : Type*) [Fintype σ] (n : ℕ)
    [Fintype {m : σ →₀ ℕ // m.degree = n}] :
    Fintype.card {m : σ →₀ ℕ // m.degree = n} =
      Nat.multichoose (Fintype.card σ) n := by
  classical
  rw [Fintype.card_congr (degreeEquivSym σ n), Sym.card_sym_eq_multichoose]

end SerrePositivity.HilbertSerre

end Monomials

section PolynomialSeries

namespace SerrePositivity.HilbertSerre

open MvPolynomial

variable (k : Type u) [Field k]

/-- The monomial basis of homogeneous polynomials of fixed total degree. -/
def homogeneousBasis (σ : Type v) (n : ℕ) :
    Module.Basis {m : σ →₀ ℕ // m.degree = n} k (homogeneousSubmodule σ k n) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact basisRestrictSupport k {m | m.degree = n}

/-- The dimension of the degree `n` component is the number of monomials of that degree. -/
theorem finrank_homogeneousSubmodule (σ : Type v) [Fintype σ] (n : ℕ) :
    Module.finrank k (homogeneousSubmodule σ k n) =
      Nat.multichoose (Fintype.card σ) n := by
  classical
  let : Fintype {m : σ →₀ ℕ // m.degree = n} := (Finsupp.finite_of_degree_eq n).fintype
  rw [Module.finrank_eq_card_basis (homogeneousBasis k σ n)]
  exact card_degree_eq_multichoose σ n

/-- Over a field, homogeneous degree length is its monomial count. -/
theorem length_homogeneousSubmodule (σ : Type v) [Fintype σ] (n : ℕ) :
    Module.length k (homogeneousSubmodule σ k n) =
      (Nat.multichoose (Fintype.card σ) n : ℕ∞) := by
  let : Module.Finite k (homogeneousSubmodule σ k n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg σ k n)
  rw [Module.length_eq_finrank, finrank_homogeneousSubmodule]

/-- Every homogeneous component has finite length. -/
theorem finiteLength_homogeneousSubmodule (σ : Type v) [Finite σ] (n : ℕ) :
    IsFiniteLength k (homogeneousSubmodule σ k n) := by
  let : Fintype σ := Fintype.ofFinite σ
  apply Module.length_ne_top_iff.mp
  rw [length_homogeneousSubmodule]
  exact ENat.natCast_ne_top _

/-- The inverse power of `1-X` has the multichoose coefficients, including exponent zero. -/
theorem coeff_invOneSubPow_eq_multichoose (s n : ℕ) :
    PowerSeries.coeff n (PowerSeries.invOneSubPow ℚ s).val = (Nat.multichoose s n : ℚ) := by
  cases s with
  | zero =>
    cases n <;> simp [PowerSeries.invOneSubPow_zero, Nat.multichoose_zero_right,
      Nat.multichoose_zero_succ]
  | succ s =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk,
      Nat.multichoose_eq]
    congr 1
    rw [show s + 1 + n - 1 = s + n by omega, Nat.choose_symm_add]

/-- The homogeneous-length series of the polynomial ring is `(1-X)⁻ˢ`. -/
theorem lengthSeries_homogeneousSubmodule (s : ℕ) :
    HilbertSerre.lengthSeries (homogeneousSubmodule (Fin s) k) =
      (PowerSeries.invOneSubPow ℚ s).val := by
  ext n
  rw [HilbertSerre.lengthSeries, PowerSeries.coeff_mk, length_homogeneousSubmodule,
    ENat.toNat_natCast, Fintype.card_fin, coeff_invOneSubPow_eq_multichoose]

end SerrePositivity.HilbertSerre

end PolynomialSeries

section Relations

namespace SerrePositivity.HilbertSerre

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

end SerrePositivity.HilbertSerre

end Relations
