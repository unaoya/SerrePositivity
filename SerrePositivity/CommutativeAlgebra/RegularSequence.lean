module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.Algebra.Category.ModuleCat.Basic
/-!
# 極大イデアルの正則生成列から得られる一般論

Noether 局所環の極大イデアルが正則列で生成されるとき、その環が整域であることと、
有限自由加群による分解の第 `d` 核が自由になることを証明する（`d` は生成列の長さ）。
正則局所環の次元による定義は仮定しない。

整域性には Krull の共通部分定理を使う。分解の核の自由性には、正則元で割った短完全列の
完全性と、Mathlib の `Module.free_quotSMulTop_iff_free` を使う。
-/

@[expose] public section

open IsLocalRing
namespace SerrePositivity
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
end SerrePositivity
