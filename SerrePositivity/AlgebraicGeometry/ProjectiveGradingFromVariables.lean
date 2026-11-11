module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Module.GradedModule

/-!
概要：変数が次数を一つ上げるという条件から、多項式環の次数付き作用を作る。
方針：単項式を指数の有限台で帰納し、斉次多項式をその単項式の和へ展開する。
規約：次数成分は係数環上の部分加群として与える。
使われ方：基底 Rees 環上の多項式作用と、Rees 加群の Proj 次数の両立性。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

variable {B ι N : Type*} [CommRing B] [AddCommGroup N] [Module B N]
variable [Module (MvPolynomial ι B) N] [IsScalarTower B (MvPolynomial ι B) N]
variable (G : ℕ → Submodule B N)
variable (hX : ∀ i j, ∀ m ∈ G j, (MvPolynomial.X i : MvPolynomial ι B) • m ∈ G (j + 1))

include hX

/-- 変数の作用の反復は、冪の数だけ次数を上げる。 -/
theorem projectiveGrading_X_pow_mem (i : ι) (k j : ℕ) (m : N) (hm : m ∈ G j) :
    (MvPolynomial.X i : MvPolynomial ι B) ^ k • m ∈ G (k + j) := by
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    simpa only [pow_succ', mul_smul, Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using hX i (k + j) _ ih

/-- 単項式の作用は、指数の全和だけ次数を上げる。 -/
theorem projectiveGrading_monomial_mem (e : ι →₀ ℕ) (b : B)
    (j : ℕ) (m : N) (hm : m ∈ G j) :
    MvPolynomial.monomial e b • m ∈ G (e.degree + j) := by
  classical
  induction e using Finsupp.induction generalizing j m with
  | zero => simpa only [map_zero, zero_add, MvPolynomial.monomial_zero', MvPolynomial.C_eq_algebraMap,
      algebraMap_smul] using (G j).smul_mem b hm
  | single_add i k e hi hk ih =>
    rw [MvPolynomial.monomial_single_add, mul_smul]
    simpa only [map_add, Finsupp.degree_single, add_assoc] using
      projectiveGrading_X_pow_mem G hX i k (e.degree + j) _ (ih j m hm)

/-- 標準変数の作用の次数だけから、多項式環の次数付き作用が得られる。 -/
theorem projectiveGradedSMul_of_variables :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B) G := by
  classical
  refine ⟨?_⟩
  intro i j p m hp hm
  change p • m ∈ G (i + j)
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported] at hp
  rw [p.as_sum, Finset.sum_smul]
  apply Submodule.sum_mem
  intro e he
  have hed : e.degree = i := hp he
  simpa only [hed] using projectiveGrading_monomial_mem G hX e (p.coeff e) j m hm

end SerrePositivity.AlgebraicGeometry
