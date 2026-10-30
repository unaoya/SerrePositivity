module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Graded.Subquotient
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.PolynomialGrowth
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.Algebra.Ring.GeomSum

/-! # 次数付き加群の Hilbert 級数と Hilbert–Serre の定理

## 概要

有限長の成分を持つ次数付き加群の長さ級数 `lengthSeries` を定義し、次数を上げる写像の核・余核による
漸化式、有限生成な次数付き加群の Hilbert 級数が `(1 - X)^{-s}` 型の有理式になること（Hilbert–Serre）、
累積長さの多項式性、次数を保つ全射による累積長さの比較を示す。

## 方針

次数 `d` の写像の各次数での完全列（`Graded/Subquotient` の一般 API）から級数の漸化式を得て、
生成元の個数の帰納法で有理性を示す。累積長さは `1/(1 - X)` を掛けた級数として扱う。

## 規約

名前空間は `HilbertSerre`。級数は ℚ 係数の `PowerSeries`。

## 使われ方

Samuel 多項式の存在と次数（`HilbertSamuel/Polynomial`）、多項式環の Hilbert 級数（`Graded/PolynomialRing`）、
Koszul ホモロジーの次数付け（`GradedKoszulHomology`）。
-/

@[expose] public noncomputable section

universe u v w

section LengthSeries

namespace SerrePositivity.HilbertSerre

open DirectSum

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
variable (N : ℕ → Submodule R M) [Decomposition N]

/-- 各次数の長さを係数とする級数。 -/
def lengthSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((Module.length R (N n)).toNat : ℚ)

/-- 各次数の元を含む部分加群への単射。 -/
def submoduleGradeInclusion (S : Submodule R M) (n : ℕ) :
    submoduleGrade N S n →ₗ[R] N n where
  toFun x := ⟨x.1.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Decomposition N] in
lemma submoduleGradeInclusion_injective (S : Submodule R M) (n : ℕ) :
    Function.Injective (submoduleGradeInclusion N S n) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : N n => (z : M)) h

variable (hfinite : ∀ n, IsFiniteLength R (N n))

omit [Decomposition N] in
include hfinite in
lemma finiteLength_submoduleGrade (S : Submodule R M) (n : ℕ) :
    IsFiniteLength R (submoduleGrade N S n) :=
  (hfinite n).of_injective (f := submoduleGradeInclusion N S n)
    (submoduleGradeInclusion_injective N S n)

omit [Decomposition N] in
include hfinite in
lemma finiteLength_quotientGrade (S : Submodule R M) (n : ℕ) :
    IsFiniteLength R (quotientGrade N S n) := by
  let f : N n →ₗ[R] quotientGrade N S n :=
    (S.mkQ.comp (N n).subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact (hfinite n).of_surjective (f := f) hf

variable (f : M →ₗ[R] M)
variable (hdegree : ∀ n, ∀ x ∈ N n, f x ∈ N (n + 1))

include hfinite hdegree

/-- 四項完全列の長さの加法性。 -/
lemma component_length_identity (n : ℕ) :
    ((Module.length R (N (n + 1))).toNat : ℚ) +
      ((Module.length R (submoduleGrade N f.ker n)).toNat : ℚ) =
    ((Module.length R (N n)).toNat : ℚ) +
      ((Module.length R (quotientGrade N f.range (n + 1))).toNat : ℚ) := by
  let d := componentMap N N f hdegree n
  let g := quotientComponent N f (n + 1)
  have h1q : ((Module.length R (N n)).toNat : ℚ) =
      ((Module.length R d.ker).toNat : ℚ) + ((Module.length R d.range).toNat : ℚ) := by
    exact_mod_cast lengthNat_ker_add_range d (hfinite n)
  have h2q : ((Module.length R (N (n + 1))).toNat : ℚ) =
      ((Module.length R g.ker).toNat : ℚ) +
        ((Module.length R (quotientGrade N f.range (n + 1))).toNat : ℚ) := by
    exact_mod_cast lengthNat_add_of_exact g.ker.subtype g
      (Submodule.subtype_injective _) (quotientComponent_surjective N f (n + 1))
      (LinearMap.exact_subtype_ker_map g) (hfinite (n + 1))
  rw [(componentMap_quotientComponent_exact N N f hdegree n).linearMap_ker_eq] at h2q
  rw [(kernelGradeEquiv N N f hdegree n).length_eq]
  linarith

omit hfinite in
/-- 第零次には流入する写像がないので、余核の第零次は元の第零次に等しい。 -/
lemma length_quotientGrade_zero : Module.length R (quotientGrade N f.range 0) =
    Module.length R (N 0) :=
  (LinearEquiv.ofBijective (quotientComponent N f 0)
    ⟨quotientComponent_injective_of_lt N N f hdegree 0 (by omega),
      quotientComponent_surjective N f 0⟩).length_eq.symm

/-- 次数一の写像の核・余核による Hilbert 級数の漸化式。 -/
theorem one_sub_X_mul_lengthSeries :
    (1 - PowerSeries.X) * lengthSeries N =
      lengthSeries (quotientGrade N f.range) -
        PowerSeries.X * lengthSeries (submoduleGrade N f.ker) := by
  ext n
  cases n with
  | zero =>
    simp [lengthSeries, length_quotientGrade_zero N f hdegree]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      lengthSeries, PowerSeries.coeff_mk]
    have h := component_length_identity N hfinite f hdegree n
    linarith

end SerrePositivity.HilbertSerre

end LengthSeries

section Finite

namespace SerrePositivity.HilbertSerre

open Polynomial DirectSum
open scoped DirectSum

variable (A : Type u) [CommRing A]
section polynomial

variable (M : Type u) [AddCommGroup M] [Module A M] [Module A[X] M]
    [IsScalarTower A A[X] M]

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

end Finite

section HilbertSerre

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
      ker_isHomogeneous_of_degree N N f hfdegree
    have hCh : (fp.range.restrictScalars R).IsHomogeneous N :=
      range_isHomogeneous_of_degree N N f hfdegree
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
    have hinv := one_sub_X_mul_invOneSubPow_one
    refine ⟨QC - X * QK, ?_⟩
    calc
      lengthSeries N = ((1 - PowerSeries.X) * lengthSeries N) *
          (PowerSeries.invOneSubPow ℚ 1).val := by rw [mul_right_comm, hinv, one_mul]
      _ = _ := by
        rw [hrec, PowerSeries.invOneSubPow_add, Units.val_mul,
          Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_X]
        ring

end SerrePositivity.HilbertSerre

end HilbertSerre

section ShiftMap

namespace SerrePositivity.HilbertSerre

open DirectSum

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
variable (N : ℕ → Submodule R M) [Decomposition N] (f : M →ₗ[R] M) (d : ℕ)
variable (hdegree : ∀ n, ∀ x ∈ N n, f x ∈ N (n + d))

include hdegree

/-- Below the degree of the relation the quotient has the original components. -/
lemma length_quotientGrade_below (n : ℕ) (hn : n < d) :
    Module.length R (quotientGrade N f.range n) = Module.length R (N n) :=
  (LinearEquiv.ofBijective (quotientComponent N f n)
    ⟨quotientComponent_injective_of_lt N N f hdegree n hn,
      quotientComponent_surjective N f n⟩).length_eq.symm

/-- Multiplication by a nonzero homogeneous relation in a domain gives this exact sequence. -/
lemma length_component_eq_add (hf : Function.Injective f) (n : ℕ) :
    Module.length R (N (n + d)) =
      Module.length R (N n) + Module.length R (quotientGrade N f.range (n + d)) :=
  Module.length_eq_add_of_exact (componentMap N N f hdegree n)
    (quotientComponent N f (n + d)) (componentMap_injective N N f hdegree hf n)
    (quotientComponent_surjective N f (n + d))
    (componentMap_quotientComponent_exact N N f hdegree n)

/-- The Hilbert series of the quotient by an injective degree-`d` map is `(1-X^d)H`. -/
theorem lengthSeries_quotient_eq (hfinite : ∀ n, IsFiniteLength R (N n))
    (hf : Function.Injective f) :
    lengthSeries (quotientGrade N f.range) =
      (1 - PowerSeries.X ^ d) * lengthSeries N := by
  ext n
  simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul',
    lengthSeries, PowerSeries.coeff_mk]
  by_cases hn : d ≤ n
  · rw [ite_eq_left hn]
    have h := length_component_eq_add N f d hdegree hf (n - d)
    rw [Nat.sub_add_cancel hn] at h
    have hq := finiteLength_quotientGrade N hfinite f.range n
    have hc := congrArg (fun a : ℕ∞ => (a.toNat : ℚ)) h
    rw [ENat.toNat_add (Module.length_ne_top_iff.mpr (hfinite (n - d)))
      (Module.length_ne_top_iff.mpr hq), Nat.cast_add] at hc
    linarith
  · rw [ite_eq_right hn, sub_zero, length_quotientGrade_below N f d hdegree n (by omega)]

end SerrePositivity.HilbertSerre

end ShiftMap

section Cumulative

namespace SerrePositivity.HilbertSerre

open Polynomial Filter

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- The cumulative numerical length of the components of degree strictly less than `n`. -/
def cumulativeLength (N : ℕ → Submodule R M) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, ((Module.length R (N i)).toNat : ℚ)

def cumulativeSeries (N : ℕ → Submodule R M) : PowerSeries ℚ :=
  PowerSeries.mk (cumulativeLength N)

lemma cumulativeLength_succ (N : ℕ → Submodule R M) (n : ℕ) :
    cumulativeLength N (n + 1) =
      cumulativeLength N n + ((Module.length R (N n)).toNat : ℚ) := by
  simp only [cumulativeLength, Finset.sum_range_succ]

/-- Passing from the component series to the cumulative series adds one denominator factor. -/
theorem one_sub_X_mul_cumulativeSeries (N : ℕ → Submodule R M) :
    (1 - PowerSeries.X) * cumulativeSeries N = PowerSeries.X * lengthSeries N := by
  ext n
  cases n with
  | zero => simp [cumulativeSeries, cumulativeLength]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      cumulativeSeries, lengthSeries, PowerSeries.coeff_mk, cumulativeLength_succ]
    ring

theorem cumulativeSeries_eq (N : ℕ → Submodule R M) :
    cumulativeSeries N = PowerSeries.X * lengthSeries N *
      (PowerSeries.invOneSubPow ℚ 1).val := by
  have hinv := one_sub_X_mul_invOneSubPow_one
  calc
    cumulativeSeries N = ((1 - PowerSeries.X) * cumulativeSeries N) *
        (PowerSeries.invOneSubPow ℚ 1).val := by rw [mul_right_comm, hinv, one_mul]
    _ = _ := by rw [one_sub_X_mul_cumulativeSeries]

/-- A rational component series with denominator exponent `s` gives a cumulative
polynomial of degree at most `s`. -/
theorem exists_cumulativePoly_of_lengthSeries (N : ℕ → Submodule R M) (s : ℕ) (Q : ℚ[X])
    (hseries : lengthSeries N = Q * (PowerSeries.invOneSubPow ℚ s).val) :
    ∃ P : ℚ[X], (∀ᶠ n : ℕ in atTop, cumulativeLength N n = P.eval (n : ℚ)) ∧
      P.natDegree ≤ s :=
  exists_poly_eventually_eq_partialSum _ s Q hseries

/-- The numerator `1-X^d` cancels one denominator factor, without any formal division. -/
lemma one_sub_X_pow_mul_invOneSubPow (d s : ℕ) :
    (1 - PowerSeries.X ^ d) * (PowerSeries.invOneSubPow ℚ (s + 1)).val =
      ((∑ i ∈ Finset.range d, X ^ i : ℚ[X]) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ s).val := by
  have hg : (1 - PowerSeries.X ^ d : PowerSeries ℚ) =
      (1 - PowerSeries.X) * ((∑ i ∈ Finset.range d, X ^ i : ℚ[X]) : PowerSeries ℚ) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow, Polynomial.coe_X]
    have h := geom_sum_mul (PowerSeries.X : PowerSeries ℚ) d
    linear_combination h
  have hi := one_sub_X_mul_invOneSubPow_one
  rw [hg, PowerSeries.invOneSubPow_add, Units.val_mul]
  calc
    _ = ((∑ i ∈ Finset.range d, X ^ i : ℚ[X]) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ s).val *
        ((1 - PowerSeries.X) * (PowerSeries.invOneSubPow ℚ 1).val) := by ring
    _ = _ := by rw [hi, mul_one]

/-- The quotient by an injective homogeneous map has a cumulative polynomial with
one smaller degree bound than its source denominator exponent. -/
theorem exists_cumulativePoly_quotient_of_injective
    (N : ℕ → Submodule R M) [DirectSum.Decomposition N]
    (hfinite : ∀ n, IsFiniteLength R (N n)) (f : M →ₗ[R] M) (d : ℕ)
    (hdegree : ∀ n, ∀ x ∈ N n, f x ∈ N (n + d)) (hf : Function.Injective f)
    (s : ℕ) (Q : ℚ[X])
    (hseries : lengthSeries N = Q * (PowerSeries.invOneSubPow ℚ (s + 1)).val) :
    ∃ P : ℚ[X],
      (∀ᶠ n : ℕ in atTop, cumulativeLength (quotientGrade N f.range) n = P.eval (n : ℚ)) ∧
      P.natDegree ≤ s := by
  apply exists_cumulativePoly_of_lengthSeries (quotientGrade N f.range) s
    ((∑ i ∈ Finset.range d, X ^ i) * Q)
  rw [lengthSeries_quotient_eq N f d hdegree hfinite hf, hseries,
    mul_left_comm, one_sub_X_pow_mul_invOneSubPow, Polynomial.coe_mul]
  ring

/-- Any eventually smaller cumulative function represented by a polynomial with positive
leading coefficient inherits the degree bound. -/
theorem natDegree_le_of_cumulative_quotient_bound
    (N : ℕ → Submodule R M) [DirectSum.Decomposition N]
    (hfinite : ∀ n, IsFiniteLength R (N n)) (f : M →ₗ[R] M) (d : ℕ)
    (hdegree : ∀ n, ∀ x ∈ N n, f x ∈ N (n + d)) (hf : Function.Injective f)
    (s : ℕ) (Q : ℚ[X])
    (hseries : lengthSeries N = Q * (PowerSeries.invOneSubPow ℚ (s + 1)).val)
    (P : ℚ[X]) (hP : 0 < P.leadingCoeff)
    (hbound : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) ≤ cumulativeLength (quotientGrade N f.range) n) :
    P.natDegree ≤ s := by
  obtain ⟨T, hT, hdeg⟩ :=
    exists_cumulativePoly_quotient_of_injective N hfinite f d hdegree hf s Q hseries
  apply (natDegree_le_of_eventually_eval_le hP ?_).trans hdeg
  filter_upwards [hbound, hT] with n hn hTn
  rwa [hTn] at hn

end SerrePositivity.HilbertSerre

end Cumulative

section Surjection

namespace SerrePositivity.HilbertSerre

open DirectSum

set_option backward.isDefEq.respectTransparency false

variable {R M T : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup T] [Module R T]
variable (NS : ℕ → Submodule R M) (NT : ℕ → Submodule R T)
variable [Decomposition NS] [Decomposition NT] (F : M →ₗ[R] T)
variable (hdegree : ∀ n, ∀ x ∈ NS n, F x ∈ NT n)

include hdegree

/-- 次数を保つ写像と成分射影の可換性（`gradeProjection_comp_of_degree` の `d = 0` の場合）。 -/
lemma gradeProjection_comp (n : ℕ) :
    (gradeProjection NT n).comp F = F.comp (gradeProjection NS n) :=
  gradeProjection_comp_of_degree NS NT F (d := 0) hdegree n

/-- The map on a component, after factoring out a submodule killed by `F`. -/
def quotientGradeMap (S : Submodule R M) (hS : S ≤ F.ker) (n : ℕ) :
    quotientGrade NS S n →ₗ[R] NT n :=
  ((S.liftQ F hS).comp (quotientGrade NS S n).subtype).codRestrict (NT n) (by
    intro x
    obtain ⟨m, hm, heq⟩ := x.2
    change (S.liftQ F hS) (x : M ⧸ S) ∈ NT n
    rw [← heq]
    exact hdegree n m hm)

/-- A global graded surjection remains surjective on each component of a relation quotient. -/
lemma quotientGradeMap_surjective (hf : Function.Surjective F)
    (S : Submodule R M) (hS : S ≤ F.ker) (n : ℕ) :
    Function.Surjective (quotientGradeMap NS NT F hdegree S hS n) := by
  intro y
  obtain ⟨m, hm⟩ := hf (y : T)
  let x : NS n := ⟨gradeProjection NS n m, (DirectSum.decompose NS m n).2⟩
  refine ⟨⟨S.mkQ x, ⟨x, x.2, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change F (gradeProjection NS n m) = (y : T)
  have h := DFunLike.congr_fun (gradeProjection_comp NS NT F hdegree n) m
  simp only [LinearMap.comp_apply] at h
  rw [hm, gradeProjection_same NT n y.2] at h
  exact h.symm

lemma length_le_quotientGrade_of_surjective (hf : Function.Surjective F)
    (S : Submodule R M) (hS : S ≤ F.ker) (n : ℕ) :
    Module.length R (NT n) ≤ Module.length R (quotientGrade NS S n) :=
  Module.length_le_of_surjective (quotientGradeMap NS NT F hdegree S hS n)
    (quotientGradeMap_surjective NS NT F hdegree hf S hS n)

/-- The target cumulative growth is bounded by that of any killed relation quotient. -/
theorem cumulativeLength_le_quotient_of_surjective
    (hfinite : ∀ n, IsFiniteLength R (NS n)) (hf : Function.Surjective F)
    (S : Submodule R M) (hS : S ≤ F.ker) (n : ℕ) :
    cumulativeLength NT n ≤ cumulativeLength (quotientGrade NS S) n := by
  apply Finset.sum_le_sum
  intro i _
  have h := length_le_quotientGrade_of_surjective NS NT F hdegree hf S hS i
  have hq := finiteLength_quotientGrade NS hfinite S i
  exact_mod_cast ENat.toNat_le_toNat h (Module.length_ne_top_iff.mpr hq)

end SerrePositivity.HilbertSerre

end Surjection
