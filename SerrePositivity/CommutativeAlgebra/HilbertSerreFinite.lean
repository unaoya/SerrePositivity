module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.DirectSum.Decomposition

/-! # Hilbert–Serre の有限生成性に関する補題

次数一の変数で消える加群の有限生成性を、その変数を除いた係数環へ移す。
また、有限生成加群の非負次数分解は、係数環上有限生成なら高次で零になる。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSerre

open Polynomial DirectSum
open scoped DirectSum

variable (A : Type u) [CommRing A]
section polynomial

variable (M : Type u) [AddCommGroup M] [Module A M] [Module A[X] M]
    [IsScalarTower A A[X] M]

/-- X が零作用なら、任意の多項式の作用は定数項の作用に等しい。 -/
lemma polynomial_smul_eq_eval_zero (hX : ∀ m : M, (X : A[X]) • m = 0)
    (p : A[X]) (m : M) : p • m = p.eval 0 • m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_smul, hp, hq, eval_add, add_smul]
  | monomial n a =>
    cases n with
    | zero =>
      rw [monomial_zero_left, eval_C]
      change algebraMap A A[X] a • m = a • m
      exact algebraMap_smul A[X] a m
    | succ n =>
      rw [eval_monomial, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_smul,
        ← C_mul_X_pow_eq_monomial, pow_succ, mul_smul, mul_smul, hX, smul_zero, smul_zero]

/-- A[X] 上有限生成で X が零作用なら、A 上でも有限生成。 -/
theorem finite_of_polynomial_X_zero [Module.Finite A[X] M]
    (hX : ∀ m : M, (X : A[X]) • m = 0) : Module.Finite A M := by
  let f : M →ₛₗ[Polynomial.evalRingHom (0 : A)] M :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun p m => polynomial_smul_eq_eval_zero A M hX p m }
  exact Module.Finite.of_surjective f Function.surjective_id

end polynomial

section multivariate

variable {A} {M : Type u} [AddCommGroup M]
variable {s : ℕ} [Module (MvPolynomial (Fin (s + 1)) A) M]

/-- 第零変数を零にし、残りの変数を一つ繰り上げて添字を戻す。 -/
def dropFirstVariable :
    MvPolynomial (Fin (s + 1)) A →ₐ[A] MvPolynomial (Fin s) A :=
  MvPolynomial.aeval (Fin.cases 0 fun i => MvPolynomial.X i)

/-- 第零変数を除いた多項式環の作用。 -/
@[instance_reducible]
def smallerPolynomialModule : Module (MvPolynomial (Fin s) A) M :=
  Module.compHom M (MvPolynomial.rename Fin.succ).toRingHom

/-- 第零変数が零作用なら、多項式の作用はその変数を零にしたものの作用に等しい。 -/
lemma smul_eq_dropFirstVariable
    (hX : ∀ m : M, (MvPolynomial.X (0 : Fin (s + 1)) : MvPolynomial (Fin (s + 1)) A) • m = 0)
    (p : MvPolynomial (Fin (s + 1)) A) (m : M) :
    let _ := smallerPolynomialModule (A := A) (M := M) (s := s)
    p • m = dropFirstVariable p • m := by
  let := smallerPolynomialModule (A := A) (M := M) (s := s)
  change p • m = (dropFirstVariable p : MvPolynomial (Fin s) A) • m
  have hC (a : A) (m : M) : (MvPolynomial.C a : MvPolynomial (Fin (s + 1)) A) • m =
      (MvPolynomial.C a : MvPolynomial (Fin s) A) • m := by
    change _ = (MvPolynomial.rename (Fin.succ : Fin s → Fin (s + 1))
      (MvPolynomial.C a : MvPolynomial (Fin s) A)) • m
    rw [MvPolynomial.rename_C]
  have hvar (i : Fin (s + 1)) (m : M) :
      (MvPolynomial.X i : MvPolynomial (Fin (s + 1)) A) • m =
        dropFirstVariable (MvPolynomial.X i : MvPolynomial (Fin (s + 1)) A) • m := by
    cases i using Fin.cases with
    | zero => simp [dropFirstVariable, hX]
    | succ i =>
      rw [dropFirstVariable, MvPolynomial.aeval_X]
      change _ = (MvPolynomial.rename (Fin.succ : Fin s → Fin (s + 1))
        (MvPolynomial.X i : MvPolynomial (Fin s) A)) • m
      rw [MvPolynomial.rename_X]
  induction p using MvPolynomial.induction_on generalizing m with
  | C a => simpa [dropFirstVariable] using hC a m
  | add p q hp hq => rw [add_smul, hp, hq, map_add, add_smul]
  | mul_X p i hp => rw [mul_smul, hp, map_mul, mul_smul, hvar]

/-- 多変数多項式環上有限生成で一つの変数が零作用なら、残りの変数上でも有限生成。 -/
theorem finite_smallerPolynomialModule [Module.Finite (MvPolynomial (Fin (s + 1)) A) M]
    (hX : ∀ m : M, (MvPolynomial.X (0 : Fin (s + 1)) : MvPolynomial (Fin (s + 1)) A) • m = 0) :
    let _ := smallerPolynomialModule (A := A) (M := M) (s := s)
    Module.Finite (MvPolynomial (Fin s) A) M := by
  let := smallerPolynomialModule (A := A) (M := M) (s := s)
  let f : M →ₛₗ[dropFirstVariable.toRingHom] M :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun p m => smul_eq_dropFirstVariable hX p m }
  exact Module.Finite.of_surjective f Function.surjective_id

/-- 変数を除く係数制限は、元の係数環の作用と両立する。 -/
theorem smallerPolynomialModule_scalarTower [Module A M]
    [IsScalarTower A (MvPolynomial (Fin (s + 1)) A) M] :
    let _ := smallerPolynomialModule (A := A) (M := M) (s := s)
    IsScalarTower A (MvPolynomial (Fin s) A) M := by
  let := smallerPolynomialModule (A := A) (M := M) (s := s)
  apply IsScalarTower.of_algebraMap_smul
  intro a m
  change (MvPolynomial.rename (Fin.succ : Fin s → Fin (s + 1))
    (MvPolynomial.C a : MvPolynomial (Fin s) A)) • m = a • m
  rw [MvPolynomial.rename_C]
  exact algebraMap_smul (MvPolynomial (Fin (s + 1)) A) a m

end multivariate

section bounded

variable {A} {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable (N : ℕ → Submodule A M) [Decomposition N]

/-- 係数環上有限生成なら、内部直和分解の高次成分は零になる。 -/
theorem exists_bound_grade_eq_bot : ∃ b : ℕ, ∀ n ≥ b, N n = ⊥ := by
  classical
  obtain ⟨k, v, hv⟩ := Module.Finite.exists_fin (R := A) (M := M)
  let supports : Finset ℕ := Finset.univ.biUnion fun i => (DirectSum.decompose N (v i)).support
  refine ⟨supports.sup id + 1, fun n hn => ?_⟩
  have hnv (i : Fin k) : DirectSum.decompose N (v i) n = 0 := by
    apply DFinsupp.notMem_support_iff.mp
    intro hi
    have hin : n ∈ supports := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
    have hle : n ≤ supports.sup id := Finset.le_sup (f := id) hin
    omega
  let p : M →ₗ[A] N n := (DirectSum.component A ℕ (fun n => N n) n).comp
    (DirectSum.decomposeLinearEquiv N).toLinearMap
  have hp : p = 0 := by
    apply LinearMap.ext_on_range hv
    intro i
    exact hnv i
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hpx : p x = 0 := by rw [hp, LinearMap.zero_apply]
  have hsame : (p x : M) = x := DirectSum.decompose_of_mem_same N hx
  exact hsame.symm.trans (congrArg Subtype.val hpx)

end bounded

end SerrePositivity.HilbertSerre
