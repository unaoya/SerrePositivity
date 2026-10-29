module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # 正則列の一般の補題

## 概要

Noether 局所環 `R` の正則列について、論文と正則局所環の理論で使う基本的な事実を集める。
- 極大イデアルを生成する弱正則列があれば `R` は整域（`isDomain_of_regular_generators`）。
  正則局所環が整域であることの核心。`R/(x)` が整域で `x` が正則なら `R` も整域
  （`isDomain_of_quotient_span_singleton`）。
- 極大イデアルを生成する長さ `d` の弱正則列があれば、有限生成加群の有限自由分解の第 `d` 核は自由
  （`free_syzygy_of_regular_generators`）。
- 素イデアル `p` で割った商で `x` が正則であることと `x ∉ p` は同値
  （`isSMulRegular_quotient_iff_notMem_prime`）。
- 正則元 `r` で `R/(r)` が被約なら、`r^{kn} ∣ x^k` から `r^n ∣ x`（`regular_pow_dvd_of_pow_dvd`）。
- 弱正則列の全項の符号を変えても弱正則（`isWeaklyRegular_map_neg`）。

## 方針

整域性は列の長さの帰納法で、`R/(x)` が整域であることを Krull の交叉定理
（`exists_pow_mul_not_dvd`）で `R` へ持ち上げる。

## 規約

正則列は Mathlib の `RingTheory.Sequence.IsWeaklyRegular`・`IsRegular` を使う。

## 使われ方

正則局所環の整域性（`RegularLocalRing`）、有限自由分解（`HomologicalAlgebra/FiniteFreeResolution`）、
深さの補題（`Depth`）、根の塔の Frobenius 核（`RootTower`）、CLMST、BhattScholze のモニック関係
（`MonicRelationRegularSequence`）。Mathlib への提出候補（mathlib-upstream の G9）。
-/

@[expose] public noncomputable section

universe u v

open IsLocalRing

namespace SerrePositivity

section Basic

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
/-- Noether 局所環で、極大イデアルの元 `x` に関する非零元の位数は有限である。
非零元を `x ^ n * b` と書き、`b` は `x` で割れないようにできる。 -/
lemma exists_pow_mul_not_dvd (x a : R) (hx : x ∈ maximalIdeal R) (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ b : R, a = x ^ n * b ∧ ¬ x ∣ b := by
  classical
  have hI : Ideal.span {x} ≠ (⊤ : Ideal R) :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (Ideal.span_le.mpr (by simpa))
  have h : ∃ n : ℕ, ¬ x ^ n ∣ a := by
    by_contra! h
    apply ha
    have hm : a ∈ ⨅ n : ℕ, (Ideal.span {x}) ^ n := by
      simp only [Submodule.mem_iInf, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact h
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hI, Submodule.mem_bot] at hm
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show Nat.find h ≠ 0 by
    intro e
    simpa [e] using Nat.find_spec h)
  have hd : x ^ n ∣ a := by
    by_contra hd
    have := Nat.find_min' h hd
    omega
  obtain ⟨b, hb⟩ := hd
  refine ⟨n, b, hb, ?_⟩
  rintro ⟨c, rfl⟩
  apply Nat.find_spec h
  rw [hn]
  exact ⟨c, by simpa [pow_succ, mul_assoc] using hb⟩

/-- Noether 局所環で、極大イデアル内の非零因子 `x` による商が整域なら元の環も整域である。 -/
lemma isDomain_of_quotient_span_singleton (x : R) (hx : x ∈ maximalIdeal R)
    (hreg : IsSMulRegular R x) [IsDomain (R ⧸ Ideal.span {x})] : IsDomain R := by
  have : NoZeroDivisors R := ⟨by
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    obtain ⟨n, a', rfl, ha'⟩ := exists_pow_mul_not_dvd x a hx ha
    obtain ⟨m, b', rfl, hb'⟩ := exists_pow_mul_not_dvd x b hx hb
    have hab' : a' * b' = 0 := (hreg.pow (n + m)).right_eq_zero_of_smul (by
      simpa only [smul_eq_mul, pow_add, mul_mul_mul_comm] using hab)
    have hm := congrArg (Ideal.Quotient.mk (Ideal.span {x})) hab'
    rw [map_mul, map_zero, mul_eq_zero] at hm
    rcases hm with hm | hm
    · exact False.elim (ha' (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hm)))
    · exact False.elim (hb' (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hm)))⟩
  exact NoZeroDivisors.to_isDomain R

omit [IsNoetherianRing R] in
/-- 極大イデアルの生成列の先頭で割ると、残りの元の像が商環の極大イデアルを生成する。 -/
lemma regular_generators_quotient {rs : List R} {x : R}
    (hgen : Ideal.ofList (x :: rs) = maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span {x}))) =
      maximalIdeal (R ⧸ Ideal.span {x}) := by
  let : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hm : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
      maximalIdeal (R ⧸ Ideal.span {x}) := by
    ext a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hle : Ideal.span {x} ≤ maximalIdeal R := by
      rw [← hgen, Ideal.ofList_cons]
      exact le_sup_left
    simp [sup_eq_left.mpr hle]
  rw [← hm, ← hgen, Ideal.ofList_cons, Ideal.map_sup]
  have hz : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span {x}) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  simp [hz]

/-- 極大イデアルが弱正則列で生成される Noether 局所環は整域である。 -/
lemma isDomain_of_regular_generators (rs : List R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hgen : Ideal.ofList rs = maximalIdeal R) : IsDomain R := by
  classical
  generalize hn : rs.length = n
  induction n generalizing R with
  | zero =>
    have hm : maximalIdeal R = ⊥ := by
      simpa [List.length_eq_zero_iff.mp hn] using hgen.symm
    let hprime : (⊥ : Ideal R).IsPrime := hm ▸ (maximalIdeal.isMaximal R).isPrime
    exact IsDomain.of_bot_isPrime R
  | succ n ih =>
    cases rs with
    | nil => simp at hn
    | cons x rs =>
      have hx : x ∈ maximalIdeal R := hgen ▸ Ideal.subset_span (by simp)
      have hI : Ideal.span {x} ≠ (⊤ : Ideal R) :=
        ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
          (Ideal.span_le.mpr (by simpa))
      let : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hI
      let : IsLocalRing (R ⧸ Ideal.span {x}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      obtain ⟨hregx, hregrs⟩ :=
        (RingTheory.Sequence.isWeaklyRegular_cons_iff R x rs).mp hreg
      let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
        Submodule.quotEquivOfEq _ _ (by
          rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
      have hregs : RingTheory.Sequence.IsWeaklyRegular (R ⧸ Ideal.span {x})
          (rs.map (Ideal.Quotient.mk (Ideal.span {x}))) :=
        (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff _ _ rs).mpr
          ((e.isWeaklyRegular_congr rs).mp hregrs)
      have hgens := regular_generators_quotient hgen
      let : IsDomain (R ⧸ Ideal.span {x}) := ih _ hregs hgens (by simpa using hn)
      exact isDomain_of_quotient_span_singleton x hx hregx

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- 完全列 `M → N → L` の最初の射が単射で、`x` が `L` 上の非零因子なら、
`x` で割った最初の射も単射である。 -/
lemma quotSMulTop_map_injective {M N L : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]
    (f : M →ₗ[R] N) (g : N →ₗ[R] L) (hf : Function.Injective f)
    (he : Function.Exact f g) {x : R} (hreg : IsSMulRegular L x) :
    Function.Injective (QuotSMulTop.map x f) := by
  have hzero : Function.Exact (0 : M →ₗ[R] M) f := by
    rw [LinearMap.exact_iff, LinearMap.range_zero, LinearMap.ker_eq_bot]
    exact hf
  have h := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
    hzero he hreg
  apply LinearMap.ker_eq_bot.mp
  rw [h.linearMap_ker_eq]
  have hz : QuotSMulTop.map x (0 : M →ₗ[R] M) = 0 := map_zero _
  rw [hz, LinearMap.range_zero]

open CategoryTheory in
/-- 極大イデアルを生成する長さ `d` の正則列があれば、有限自由分解の第 `d` 核は自由である。
分解は短完全列 `0 → K (i + 1) → F i → K i → 0` の族として明示的に受け取る。
各 `K i` の有限性と各 `F i` の自由性を仮定する。正則列の先頭で割って帰納法を適用し、
Mathlib の正則元による商からの自由性の持ち上げを使う。 -/
lemma free_syzygy_of_regular_generators (rs : List R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hgen : Ideal.ofList rs = maximalIdeal R)
    (K F : ℕ → ModuleCat R) (hfinite : ∀ i, Module.Finite R (K i))
    (hfree : ∀ i, Module.Free R (F i))
    (ι : ∀ i, K (i + 1) →ₗ[R] F i) (π : ∀ i, F i →ₗ[R] K i)
    (hinj : ∀ i, Function.Injective (ι i)) (hsurj : ∀ i, Function.Surjective (π i))
    (hex : ∀ i, Function.Exact (ι i) (π i)) : Module.Free R (K rs.length) := by
  classical
  generalize hn : rs.length = n
  induction n generalizing R with
  | zero =>
    have hm : maximalIdeal R = ⊥ := by simpa [List.length_eq_zero_iff.mp hn] using hgen.symm
    let := (isField_iff_maximalIdeal_eq.mpr hm).toField
    exact Module.Free.of_divisionRing _ _
  | succ n ih =>
    cases rs with
    | nil => simp at hn
    | cons x rs =>
      have hx : x ∈ maximalIdeal R := hgen ▸ Ideal.subset_span (by simp)
      have hI : Ideal.span {x} ≠ (⊤ : Ideal R) :=
        ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
          (Ideal.span_le.mpr (by simpa))
      let : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hI
      let : IsLocalRing (R ⧸ Ideal.span {x}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      obtain ⟨hregx, hregrs⟩ := (RingTheory.Sequence.isWeaklyRegular_cons_iff R x rs).mp hreg
      let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
        Submodule.quotEquivOfEq _ _ (by
          rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
      have hregs : RingTheory.Sequence.IsWeaklyRegular (R ⧸ Ideal.span {x})
          (rs.map (Ideal.Quotient.mk (Ideal.span {x}))) :=
        (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff _ _ rs).mpr
          ((e.isWeaklyRegular_congr rs).mp hregrs)
      have hregular (i : ℕ) : IsSMulRegular (K (i + 1)) x := by
        let := hfree i
        have hF : IsSMulRegular (F i) x :=
          ((TensorProduct.lid R (F i)).isSMulRegular_congr x).mp (hregx.rTensor (F i))
        exact hF.of_injective (ι i) (hinj i)
      let K' (i : ℕ) := ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (K (i + 1)))
      let F' (i : ℕ) := ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (F (i + 1)))
      let ι' i : K' (i + 1) →ₗ[R ⧸ Ideal.span {x}] F' i :=
        (QuotSMulTop.map x (ι (i + 1))).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      let π' i : F' i →ₗ[R ⧸ Ideal.span {x}] K' i :=
        (QuotSMulTop.map x (π (i + 1))).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      have hfree' : ∀ i, Module.Free (R ⧸ Ideal.span {x}) (F' i) := by
        intro i
        let := hfree (i + 1)
        dsimp [F']
        infer_instance
      have hfinite' : ∀ i, Module.Finite (R ⧸ Ideal.span {x}) (K' i) := by
        intro i
        let := hfinite (i + 1)
        exact Module.Finite.of_restrictScalars_finite R _ _
      have hlast := ih _ hregs (regular_generators_quotient hgen) K' F' hfinite' hfree' ι' π'
        (fun i => quotSMulTop_map_injective _ _ (hinj (i + 1)) (hex (i + 1)) (hregular i))
        (fun i => QuotSMulTop.map_surjective x (hsurj (i + 1)))
        (fun i => QuotSMulTop.map_exact x (hex (i + 1)) (hsurj (i + 1))) (by simpa using hn)
      let := hfinite (n + 1)
      let := Module.finitePresentation_of_finite R (K (n + 1))
      exact (Module.free_quotSMulTop_iff_free R (K (n + 1))
        ((maximalIdeal_le_jacobson _) hx) (hregular n)).mp hlast

end Basic

section PrimeQuotient

variable {R : Type*} [CommRing R]

/-- 素イデアルの外の元は、その素イデアルによる商に正則に作用する。 -/
theorem isSMulRegular_quotient_of_notMem_prime (p : Ideal R) [p.IsPrime]
    {x : R} (hx : x ∉ p) : IsSMulRegular (R ⧸ p) x := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro y hxy
  exact (‹p.IsPrime›.mem_or_mem (show x * y ∈ p from hxy)).resolve_left hx

/-- 素イデアルによる商に正則に作用する元は、ちょうどその素イデアルの外の元。 -/
theorem isSMulRegular_quotient_iff_notMem_prime (p : Ideal R) [p.IsPrime] (x : R) :
    IsSMulRegular (R ⧸ p) x ↔ x ∉ p := by
  refine ⟨fun h hx ↦ ?_, isSMulRegular_quotient_of_notMem_prime p⟩
  have hone : (1 : R) ∈ p :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem p x).mp h 1 (by simpa using hx)
  exact ‹p.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem p hone isUnit_one)

end PrimeQuotient

section PowerDivisibility

variable (R : Type*) [CommRing R]

/-- 被約な正則主元商では、冪の整除性から元の整除性が従う。 -/
theorem regular_pow_dvd_of_pow_dvd (r : R)
    (hreg : IsLeftRegular r) [IsReduced (R ⧸ Ideal.span {r})]
    (k : ℕ) (hk : 0 < k) (n : ℕ) (x : R) (hx : r ^ (k * n) ∣ x ^ k) :
    r ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hdiv : r ∣ x ^ k :=
      dvd_trans (dvd_pow_self r (by positivity : k * (n + 1) ≠ 0)) hx
    have hz : (Ideal.Quotient.mk (Ideal.span {r}) x) ^ k = 0 := by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
    have hxr : r ∣ x := Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨k, hz⟩))
    obtain ⟨y, rfl⟩ := hxr
    have hy : r ^ (k * n) ∣ y ^ k := by
      obtain ⟨b, hb⟩ := hx
      refine ⟨b, ?_⟩
      apply hreg.pow k
      change r ^ k * y ^ k = r ^ k * (r ^ (k * n) * b)
      rw [← mul_pow, hb, Nat.mul_add, Nat.mul_one, pow_add]
      ring
    obtain ⟨b, hb⟩ := ih y hy
    refine ⟨b, ?_⟩
    rw [hb, pow_succ']
    ring

end PowerDivisibility

section MapNeg

/-- 弱正則列の全項の符号を変えても弱正則。各先行生成イデアルは変わらず、
`-1` 倍は単射だから。 -/
theorem isWeaklyRegular_map_neg {R : Type*} [CommRing R] (l : List R)
    (h : RingTheory.Sequence.IsWeaklyRegular R l) :
    RingTheory.Sequence.IsWeaklyRegular R (l.map fun x => -x) := by
  have hI (t : List R) : Ideal.ofList (t.map fun x => -x) = Ideal.ofList t := by
    induction t with
    | nil => rfl
    | cons x t ih => simp only [List.map_cons, Ideal.ofList_cons, ih, Ideal.span_singleton_neg]
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  have hr := h.regular_mod_prev i hi'
  rw [← List.map_take, hI, List.getElem_map]
  intro x y hxy
  apply hr
  exact neg_injective (by simpa only [neg_smul] using hxy)

end MapNeg

section BaseChange

open scoped TensorProduct

/-- D 上の非零因子は、平坦 A 代数 R による基底変更後も非零因子。
テンソル積上では R の左作用と、`g` の R 内の標準像を用いる。 -/
theorem isSMulRegular_tensorProduct_of_flat
    (A R D : Type u) [CommRing A] [CommRing R] [CommRing D]
    [Algebra A R] [Algebra A D] [Module.Flat A R]
    (g : A) (hg : IsSMulRegular D (algebraMap A D g)) :
    IsSMulRegular (R ⊗[A] D) (algebraMap A R g) := by
  have hg' : IsSMulRegular D g := by
    change Function.Injective (fun d : D ↦ g • d)
    change Function.Injective (fun d : D ↦ algebraMap A D g * d) at hg
    simpa only [Algebra.smul_def] using hg
  have hbase : IsSMulRegular (R ⊗[A] D) g := hg'.lTensor R
  change Function.Injective (fun x : R ⊗[A] D ↦ g • x) at hbase
  change Function.Injective (fun x : R ⊗[A] D ↦ algebraMap A R g • x)
  simpa only [IsScalarTower.algebraMap_smul] using hbase

/-- 正則な `p` について、`p` の任意の冪で消える元は零。
有界ねじれ条件では指数 `N=0` を取ることができる。 -/
theorem exists_pow_torsion_bound_of_isSMulRegular
    (S : Type u) [CommRing S] (p : ℕ) (hp : IsSMulRegular S (p : S)) :
    ∃ N : ℕ, ∀ (n : ℕ) (s : S),
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0 := by
  refine ⟨0, ?_⟩
  intro n s hs
  have hz : s = 0 := (hp.pow n).right_eq_zero_of_smul (by simpa [smul_eq_mul] using hs)
  simp [hz]

end BaseChange

end SerrePositivity
