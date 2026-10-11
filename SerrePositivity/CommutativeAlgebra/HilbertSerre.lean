module

public import SerrePositivity.CommutativeAlgebra.HilbertSerreFinite
public import SerrePositivity.CommutativeAlgebra.GradedHilbertSeries
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc

/-! # Hilbert–Serre の数値版

非負次数を持つ有限生成多項式加群で各次数が有限長なら、長さの級数は
`Q(X)/(1-X)^s` の形になる。次数一の変数の核と余核に帰納法を適用する。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSerre

open DirectSum Polynomial
open scoped DirectSum

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- Hilbert–Serre の長さ値版。長さは係数環 R 上で測る。 -/
theorem exists_rational_lengthSeries (s : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M]
      [Module (MvPolynomial (Fin s) R) M] [IsScalarTower R (MvPolynomial (Fin s) R) M]
      [Module.Finite (MvPolynomial (Fin s) R) M]
      (N : ℕ → Submodule R M) [Decomposition N],
      (∀ n, IsFiniteLength R (N n)) →
      (∀ (i : Fin s) n, ∀ x ∈ N n,
        (MvPolynomial.X i : MvPolynomial (Fin s) R) • x ∈ N (n + 1)) →
      ∃ Q : ℚ[X], lengthSeries N = Q * (PowerSeries.invOneSubPow ℚ s).val := by
  induction s with
  | zero =>
    intro M _ _ _ _ _ N _ _ _
    let : Module.Finite R (MvPolynomial (Fin 0) R) :=
      Module.Finite.of_surjective (Algebra.linearMap R _)
        (MvPolynomial.C_surjective (Fin 0))
    let : Module.Finite R M := Module.Finite.trans (MvPolynomial (Fin 0) R) M
    obtain ⟨b, hb⟩ := exists_bound_grade_eq_bot N
    refine ⟨PowerSeries.trunc b (lengthSeries N), ?_⟩
    simp only [PowerSeries.invOneSubPow_zero, Units.val_one, mul_one]
    ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    by_cases hn : n < b
    · simp [hn]
    · rw [ite_eq_right hn]
      rw [lengthSeries, PowerSeries.coeff_mk, hb n (Nat.le_of_not_gt hn)]
      simp
  | succ s ih =>
    intro M _ _ _ _ _ N _ hfinite hdegree
    let P := MvPolynomial (Fin (s + 1)) R
    let fp : M →ₗ[P] M := LinearMap.lsmul P M (MvPolynomial.X (0 : Fin (s + 1)))
    let f : M →ₗ[R] M := fp.restrictScalars R
    have hfdegree : ∀ n, ∀ x ∈ N n, f x ∈ N (n + 1) := hdegree 0
    let K := fp.ker
    let C := M ⧸ fp.range
    let NK : ℕ → Submodule R K := submoduleGrade N (fp.ker.restrictScalars R)
    let NC : ℕ → Submodule R C := quotientGrade N (fp.range.restrictScalars R)
    have hKh : (fp.ker.restrictScalars R).IsHomogeneous N :=
      kernel_isHomogeneous N f hfdegree
    have hCh : (fp.range.restrictScalars R).IsHomogeneous N :=
      range_isHomogeneous N f hfdegree
    let : Decomposition NK :=
      (isInternal_submoduleGrade N (fp.ker.restrictScalars R) hKh).chooseDecomposition
    let : Decomposition NC :=
      (isInternal_quotientGrade N (fp.range.restrictScalars R) hCh).chooseDecomposition
    have hXK : ∀ x : K, (MvPolynomial.X (0 : Fin (s + 1)) : P) • x = 0 := by
      intro x
      apply Subtype.ext
      exact x.2
    have hXC : ∀ x : C, (MvPolynomial.X (0 : Fin (s + 1)) : P) • x = 0 := by
      intro x
      obtain ⟨m, rfl⟩ := fp.range.mkQ_surjective x
      exact (fp.range.mkQ.map_smul (MvPolynomial.X (0 : Fin (s + 1))) m).symm.trans
        ((Submodule.Quotient.mk_eq_zero (p := fp.range)
          (x := (MvPolynomial.X (0 : Fin (s + 1)) : P) • m)).mpr ⟨m, rfl⟩)
    let : Module (MvPolynomial (Fin s) R) K := smallerPolynomialModule
    let : IsScalarTower R (MvPolynomial (Fin s) R) K := smallerPolynomialModule_scalarTower
    let : Module.Finite (MvPolynomial (Fin s) R) K := finite_smallerPolynomialModule hXK
    let : Module (MvPolynomial (Fin s) R) C := smallerPolynomialModule
    let : IsScalarTower R (MvPolynomial (Fin s) R) C := smallerPolynomialModule_scalarTower
    let : Module.Finite (MvPolynomial (Fin s) R) C := finite_smallerPolynomialModule hXC
    have hKfinite : ∀ n, IsFiniteLength R (NK n) :=
      finiteLength_submoduleGrade N hfinite (fp.ker.restrictScalars R)
    have hCfinite : ∀ n, IsFiniteLength R (NC n) :=
      finiteLength_quotientGrade N hfinite (fp.range.restrictScalars R)
    have hKdegree : ∀ (i : Fin s) n, ∀ x ∈ NK n,
        (MvPolynomial.X i : MvPolynomial (Fin s) R) • x ∈ NK (n + 1) := by
      intro i n x hx
      change (MvPolynomial.rename (Fin.succ : Fin s → Fin (s + 1))
        (MvPolynomial.X i : MvPolynomial (Fin s) R)) • (x : M) ∈ N (n + 1)
      rw [MvPolynomial.rename_X]
      exact hdegree i.succ n x hx
    have hCdegree : ∀ (i : Fin s) n, ∀ x ∈ NC n,
        (MvPolynomial.X i : MvPolynomial (Fin s) R) • x ∈ NC (n + 1) := by
      intro i n x hx
      obtain ⟨m, hm, rfl⟩ := hx
      change (MvPolynomial.rename (Fin.succ : Fin s → Fin (s + 1))
        (MvPolynomial.X i : MvPolynomial (Fin s) R)) • (fp.range.mkQ m : C) ∈ NC (n + 1)
      rw [MvPolynomial.rename_X, ← fp.range.mkQ.map_smul]
      change (Submodule.Quotient.mk ((MvPolynomial.X i.succ : P) • m) : C) ∈ NC (n + 1)
      exact ⟨_, hdegree i.succ n m hm, rfl⟩
    obtain ⟨QK, hK⟩ := ih K NK hKfinite hKdegree
    obtain ⟨QC, hC⟩ := ih C NC hCfinite hCdegree
    have hrec := one_sub_X_mul_lengthSeries N hfinite f hfdegree
    change (1 - PowerSeries.X) * lengthSeries N =
      lengthSeries NC - PowerSeries.X * lengthSeries NK at hrec
    rw [hK, hC] at hrec
    have hinv : (1 - PowerSeries.X) * (PowerSeries.invOneSubPow ℚ 1).val = 1 := by
      simpa only [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one] using
        (PowerSeries.invOneSubPow ℚ 1).inv_val
    refine ⟨QC - X * QK, ?_⟩
    calc
      lengthSeries N = ((1 - PowerSeries.X) * lengthSeries N) *
          (PowerSeries.invOneSubPow ℚ 1).val := by rw [mul_right_comm, hinv, one_mul]
      _ = _ := by
        rw [hrec, PowerSeries.invOneSubPow_add, Units.val_mul,
          Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_X]
        ring

end SerrePositivity.HilbertSerre
