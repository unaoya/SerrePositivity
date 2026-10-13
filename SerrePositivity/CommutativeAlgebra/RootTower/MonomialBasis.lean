module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# `R[X₁, …, X_h] / (X_i^q − s_i)` の単項式基底

## 概要

共通の根の塔の基礎として `Paper/` を import しない。今回の抽出では、互換性のため
既存の `SerrePositivity.Section2` の宣言名・定義・証明を保持する。

可換環 `R`、元 `s₁, …, s_h ∈ R`、`q ≥ 1` について、`B = R[X₁, …, X_h] / (X_i^q − s_i)_i` は
`R` 上有限自由で、`X^e`（`0 ≤ e_i < q`）が基底、ランクは `q^h`。塔の段 `A_n = A[t^{1/p^n}]`
（`CommutativeAlgebra/RootTower/Basic.lean`、`q = p^n`）に使う一般論。

## 方針

`E = (Fin h → Fin q)` を簡約された指数の集合とし、

- `Φ : (E →₀ R) → B`、`e ↦ X^e` の線形結合（`Finsupp.linearCombination`）、
- `ψ : R[X] → (E →₀ R)`、`X^d ↦ (∏ s_i^{d_i / q}) · X^{d mod q}`（単項式基底で定めた線形写像）

を作る。`ψ` は `X_i^q · f ↦ s_i · ψ f` をみたすので関係式を消し、`B` からの線形写像 `ψ̄` に降りる。
`ψ̄ ∘ Φ = id` なので `Φ` は単射。`Φ` の像は `1` を含み各 `X_i` 倍で閉じる（`e_i + 1 < q` なら
指数を上げ、`e_i + 1 = q` なら `X_i^q = s_i` で繰り下げる）ので、全射。
-/

@[expose] public section

universe u

open MvPolynomial

namespace SerrePositivity

namespace Section2

variable (R : Type u) [CommRing R] {h : ℕ} (s : Fin h → R) (q : ℕ)

/-- 関係式のイデアル `(X_i^q − s_i)_i ⊆ R[X₁, …, X_h]`。 -/
noncomputable def relIdeal : Ideal (MvPolynomial (Fin h) R) :=
  Ideal.span (Set.range fun i ↦ (X i : MvPolynomial (Fin h) R) ^ q - C (s i))

/-- 簡約された指数 `e : Fin h → Fin q` を `Fin h →₀ ℕ` とみたもの。 -/
noncomputable def expOf (e : Fin h → Fin q) : Fin h →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (e i : ℕ)

@[simp] lemma expOf_apply (e : Fin h → Fin q) (i : Fin h) : expOf q e i = e i := rfl

variable (hq : 0 < q)

/-- 指数 `d` を `q` で割った余り。 -/
def redExp (d : Fin h →₀ ℕ) : Fin h → Fin q := fun i ↦ ⟨d i % q, Nat.mod_lt _ hq⟩

/-- 繰り下がりの係数 `∏ s_i^{d_i / q}`。 -/
noncomputable def carry (d : Fin h →₀ ℕ) : R := ∏ i, s i ^ (d i / q)

lemma redExp_expOf (e : Fin h → Fin q) : redExp q hq (expOf q e) = e := by
  funext i
  exact Fin.ext (Nat.mod_eq_of_lt (e i).2)

lemma carry_expOf (e : Fin h → Fin q) : carry R s q (expOf q e) = 1 := by
  unfold carry
  exact Finset.prod_eq_one fun i _ ↦ by rw [expOf_apply, Nat.div_eq_of_lt (e i).2, pow_zero]

lemma redExp_single_add (i : Fin h) (d : Fin h →₀ ℕ) :
    redExp q hq (Finsupp.single i q + d) = redExp q hq d := by
  funext j
  apply Fin.ext
  simp only [redExp, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs with hij
  · rw [Nat.add_mod_left]
  · rw [zero_add]

include hq in
lemma carry_single_add (i : Fin h) (d : Fin h →₀ ℕ) :
    carry R s q (Finsupp.single i q + d) = s i * carry R s q d := by
  unfold carry
  have : ∀ j, s j ^ ((Finsupp.single i q + d) j / q) =
      (if j = i then s j else 1) * s j ^ (d j / q) := by
    intro j
    rw [Finsupp.add_apply, Finsupp.single_apply]
    by_cases hij : j = i
    · subst hij
      simp only [↓reduceIte, Nat.add_div_left _ hq, pow_succ, mul_comm]
    · simp only [Ne.symm hij, hij, ↓reduceIte, zero_add, one_mul]
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i (fun j ↦ s j)]
  simp

/-- 簡約写像 `ψ : R[X] → (E →₀ R)`、`X^d ↦ carry(d) · X^{d mod q}`。 -/
noncomputable def reduce : MvPolynomial (Fin h) R →ₗ[R] ((Fin h → Fin q) →₀ R) :=
  (basisMonomials (Fin h) R).constr R fun d ↦ Finsupp.single (redExp q hq d) (carry R s q d)

lemma reduce_monomial (d : Fin h →₀ ℕ) (a : R) :
    reduce R s q hq (monomial d a) = Finsupp.single (redExp q hq d) (a * carry R s q d) := by
  have : monomial d a = a • (basisMonomials (Fin h) R) d := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, reduce, Module.Basis.constr_basis, Finsupp.smul_single, smul_eq_mul]

/-- `ψ(X_i^q · f) = s_i · ψ(f)`。 -/
lemma reduce_X_pow_mul (i : Fin h) (f : MvPolynomial (Fin h) R) :
    reduce R s q hq (X i ^ q * f) = s i • reduce R s q hq f := by
  have : (reduce R s q hq).comp (LinearMap.mulLeft R (X i ^ q)) = s i • reduce R s q hq := by
    refine (basisMonomials (Fin h) R).ext fun d ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply, coe_basisMonomials]
    change reduce R s q hq (X i ^ q * monomial d 1) = s i • reduce R s q hq (monomial d 1)
    rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul, reduce_monomial, reduce_monomial,
      redExp_single_add, carry_single_add R s q hq, Finsupp.smul_single, smul_eq_mul, one_mul,
      one_mul]
  exact congrArg (fun g ↦ g f) this

/-- `ψ` は関係式を消す。 -/
lemma reduce_rel_mul (i : Fin h) (f : MvPolynomial (Fin h) R) :
    reduce R s q hq ((X i ^ q - C (s i)) * f) = 0 := by
  rw [sub_mul, map_sub, reduce_X_pow_mul, C_mul', map_smul, sub_self]

/-- 関係式のイデアルは `ψ` の核に入る。 -/
lemma relIdeal_le_ker_reduce :
    (relIdeal R s q).restrictScalars R ≤ LinearMap.ker (reduce R s q hq) := by
  intro x hx
  rw [Submodule.restrictScalars_mem, relIdeal, Ideal.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [LinearMap.mem_ker, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [mul_comm, reduce_rel_mul]

/-- `ψ` を商 `B = R[X]/(X^q − s)` に降ろしたもの。 -/
noncomputable def reduceQ :
    (MvPolynomial (Fin h) R ⧸ relIdeal R s q) →ₗ[R] ((Fin h → Fin q) →₀ R) :=
  (((relIdeal R s q).restrictScalars R).liftQ (reduce R s q hq)
    (relIdeal_le_ker_reduce R s q hq)).comp
    (Submodule.Quotient.restrictScalarsEquiv R (relIdeal R s q)).symm.toLinearMap

lemma reduceQ_mk (f : MvPolynomial (Fin h) R) :
    reduceQ R s q hq (Ideal.Quotient.mk (relIdeal R s q) f) = reduce R s q hq f := rfl

/-- 簡約された単項式の類 `X^e ∈ B`。 -/
noncomputable def redMonomial (e : Fin h → Fin q) : MvPolynomial (Fin h) R ⧸ relIdeal R s q :=
  Ideal.Quotient.mkₐ R (relIdeal R s q) (monomial (expOf q e) 1)

/-- `Φ : (E →₀ R) → B`、簡約された単項式の線形結合。 -/
noncomputable def ofRed : ((Fin h → Fin q) →₀ R) →ₗ[R] (MvPolynomial (Fin h) R ⧸ relIdeal R s q) :=
  Finsupp.linearCombination R (redMonomial R s q)

lemma reduceQ_comp_ofRed : (reduceQ R s q hq).comp (ofRed R s q) = LinearMap.id := by
  refine Finsupp.lhom_ext' fun e ↦ LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, ofRed, Finsupp.linearCombination_single,
    LinearMap.id_apply, redMonomial]
  rw [← map_smul, Ideal.Quotient.mkₐ_eq_mk, reduceQ_mk, smul_monomial, smul_eq_mul, mul_one,
    reduce_monomial, redExp_expOf, carry_expOf, mul_one]

include hq in
lemma ofRed_injective : Function.Injective (ofRed R s q) := by
  intro x y hxy
  have := congrArg (reduceQ R s q hq) hxy
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, reduceQ_comp_ofRed, LinearMap.id_apply,
    LinearMap.id_apply] at this

include hq in
/-- 簡約された単項式の張る部分加群は `X_i` 倍で閉じる。 -/
lemma redMonomial_mul_X_mem (i : Fin h) (e : Fin h → Fin q) :
    redMonomial R s q e * Ideal.Quotient.mkₐ R (relIdeal R s q) (X i) ∈
      Submodule.span R (Set.range (redMonomial R s q)) := by
  rw [redMonomial, ← map_mul, X, monomial_mul_monomial, one_mul]
  by_cases hlt : (e i : ℕ) + 1 < q
  · -- 指数を上げる
    let e' : Fin h → Fin q := Function.update e i ⟨(e i : ℕ) + 1, hlt⟩
    have : expOf q e + Finsupp.single i 1 = expOf q e' := by
      ext j
      rw [Finsupp.add_apply, expOf_apply, expOf_apply, Finsupp.single_apply]
      by_cases hji : j = i
      · subst hji
        simp [e']
      · simp [e', hji, Ne.symm hji]
    rw [this]
    exact Submodule.subset_span ⟨e', rfl⟩
  · -- `e_i + 1 = q`：`X_i^q = s_i` で繰り下げる
    have heq : (e i : ℕ) + 1 = q := le_antisymm (e i).2 (not_lt.mp hlt)
    let e'' : Fin h → Fin q := Function.update e i ⟨0, hq⟩
    have : expOf q e + Finsupp.single i 1 = expOf q e'' + Finsupp.single i q := by
      ext j
      rw [Finsupp.add_apply, Finsupp.add_apply, expOf_apply, expOf_apply, Finsupp.single_apply,
        Finsupp.single_apply]
      by_cases hji : j = i
      · subst hji
        simp [e'', heq]
      · simp [e'', hji, Ne.symm hji]
    have hsplit : (monomial (expOf q e'' + Finsupp.single i q) (1 : R)) =
        monomial (expOf q e'') 1 * X i ^ q := by
      rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul]
    rw [this, hsplit, map_mul]
    have hrel : Ideal.Quotient.mkₐ R (relIdeal R s q) ((X i : MvPolynomial (Fin h) R) ^ q) =
        Ideal.Quotient.mkₐ R (relIdeal R s q) (C (s i)) := by
      simp only [Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [hrel, ← map_mul, mul_comm, C_mul', map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e'', rfl⟩)

include hq in
lemma ofRed_surjective : Function.Surjective (ofRed R s q) := by
  rw [← LinearMap.range_eq_top, ofRed, Finsupp.range_linearCombination]
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (relIdeal R s q) x
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h0 : expOf q (fun _ : Fin h ↦ (⟨0, hq⟩ : Fin q)) = 0 := by
      ext j
      rfl
    have : Ideal.Quotient.mkₐ R (relIdeal R s q) (C a) =
        a • redMonomial R s q (fun _ ↦ ⟨0, hq⟩) := by
      rw [redMonomial, h0, ← map_smul, smul_monomial, smul_eq_mul, mul_one, C_apply]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  | add p₁ p₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | mul_X p i hp =>
    rw [map_mul]
    -- `span` の元に `X_i` を掛けたものは `span` に入る
    have hmap : (Submodule.span R (Set.range (redMonomial R s q))).map
        (LinearMap.mulRight R (Ideal.Quotient.mkₐ R (relIdeal R s q) (X i))) ≤
        Submodule.span R (Set.range (redMonomial R s q)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
      exact redMonomial_mul_X_mem R s q hq i e
    exact hmap ⟨_, hp, rfl⟩

/-- `B = R[X]/(X^q − s)` の単項式基底 `X^e`（`0 ≤ e_i < q`）。 -/
noncomputable def relBasis :
    Module.Basis (Fin h → Fin q) R (MvPolynomial (Fin h) R ⧸ relIdeal R s q) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (ofRed R s q)
    ⟨ofRed_injective R s q hq, ofRed_surjective R s q hq⟩).symm

include hq in
/-- `B` は `R` 上自由。 -/
theorem free_quotient_relIdeal : Module.Free R (MvPolynomial (Fin h) R ⧸ relIdeal R s q) :=
  Module.Free.of_basis (relBasis R s q hq)

include hq in
/-- `B` は `R` 上有限生成。 -/
theorem finite_quotient_relIdeal : Module.Finite R (MvPolynomial (Fin h) R ⧸ relIdeal R s q) :=
  Module.Finite.of_basis (relBasis R s q hq)

include hq in
/-- `B` のランクは `q^h`。 -/
theorem finrank_quotient_relIdeal [Nontrivial R] :
    Module.finrank R (MvPolynomial (Fin h) R ⧸ relIdeal R s q) = q ^ h := by
  rw [Module.finrank_eq_card_basis (relBasis R s q hq), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

end Section2

end SerrePositivity
