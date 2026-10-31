module

public import SerrePositivity.CommutativeAlgebra.Perfection
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # 両立する p 冪根が生成するイデアル

## 概要

両立する p 冪根の系を持つ元（単項でも任意の族でも）の根が生成するイデアル `compatibleRootIdeal`・`compatibleRootFamilyIdeal` を定め、冪等性・像との関係を示す。完全標数 p 環では根イデアルで割ると Frobenius が同型になる。被約環では根イデアルは平坦で（BS17 Lemma 3.16）、根イデアルのテンソル積は終域へ単射に写る。

## 方針

根イデアルは各段の単項イデアルの和として書き、平坦性は Mathlib の方程式による平坦性の判定へ直接つなぐ。

## 規約

`compatibleRootIdeal` 系の名前は BhattScholze が参照するので変えない。一般の環で根イデアルが根基であるとは主張しない。BS17 の著者版は https://people.mpim-bonn.mpg.de/scholze/Witt.pdf （p.13）。

## 使われ方

BhattScholze の André の補題（根を添加した環の perfectoid 化）。
-/

@[expose] public noncomputable section

universe u v

section CompatibleRootIdealPart

namespace SerrePositivity
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 指定された両立する根の全元が生成する具体的なイデアル。 -/
def compatibleRootIdeal (ρ : ℕ → R) : Ideal R := Ideal.span (Set.range ρ)

/-- 最初の元の主イデアルは根イデアルに含まれる。 -/
theorem span_root_zero_le_compatibleRootIdeal (ρ : ℕ → R) :
    Ideal.span {ρ 0} ≤ compatibleRootIdeal ρ :=
  (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_range_self)

/-- 根の主イデアルは単調増大する。既存の一段包含を再利用する。 -/
theorem compatibleRoot_principal_monotone (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) : Monotone (fun n ↦ Ideal.span {ρ n}) :=
  monotone_nat_of_le_succ (span_compatibleRoot_le_succ p (Fact.out : p.Prime).ne_zero ρ hρ)

/-- 根イデアルの各元は、ある一つの根の主イデアルに属する。 -/
theorem mem_compatibleRootIdeal_iff (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (x : R) :
    x ∈ compatibleRootIdeal ρ ↔ ∃ n, x ∈ Ideal.span {ρ n} := by
  rw [compatibleRootIdeal, Ideal.span_range_eq_iSup]
  exact Submodule.mem_iSup_of_directed _ (compatibleRoot_principal_monotone ρ hρ).directed_le

/-- 両立するp冪根のイデアルは冪等。B5の一般perfectoidイデアルとは区別する。 -/
theorem compatibleRootIdeal_mul_self (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    compatibleRootIdeal ρ * compatibleRootIdeal ρ = compatibleRootIdeal ρ := by
  apply le_antisymm Ideal.mul_le_left
  apply Ideal.span_le.mpr
  rintro _ ⟨n, rfl⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Fact.out : p.Prime).two_le
  rw [← hρ n, hk, pow_add, pow_two]
  exact Ideal.mul_mem_right _ (compatibleRootIdeal ρ * compatibleRootIdeal ρ)
    (Ideal.mul_mem_mul (Ideal.mem_span_range_self (x := n + 1))
      (Ideal.mem_span_range_self (x := n + 1)))

omit [Fact p.Prime] in
/-- 被約な終域への射が最初の元を消すなら、すべての根を消す。 -/
theorem compatibleRootIdeal_le_ker_of_root_zero {T : Type v} [CommRing T] [IsReduced T]
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (g : R →+* T) (hg : g (ρ 0) = 0) :
    compatibleRootIdeal ρ ≤ RingHom.ker g := by
  apply Ideal.span_le.mpr
  rintro _ ⟨n, rfl⟩
  change g (ρ n) = 0
  apply eq_zero_of_pow_eq_zero (n := p ^ n)
  have he := congrArg g (compatibleRoots_pow p ρ hρ 0 n)
  simpa only [zero_add, map_pow, hg] using he

/-- 根列を保存する射は、根イデアルを対応する根イデアルへ写す。 -/
theorem compatibleRootIdeal_map {T : Type v} [CommRing T] (ρ : ℕ → R) (g : R →+* T) :
    (compatibleRootIdeal ρ).map g = compatibleRootIdeal (fun n ↦ g (ρ n)) := by
  rw [compatibleRootIdeal, Ideal.map_span, compatibleRootIdeal, ← Set.range_comp]
  rfl

end SerrePositivity

end CompatibleRootIdealPart

section CompatibleRootFamilyIdealPart

namespace SerrePositivity
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type u}

/-- 根族の最初の元の全体が生成するイデアル。 -/
def compatibleRootFamilyZeroIdeal (ρ : σ → ℕ → R) : Ideal R :=
  Ideal.span (Set.range (fun s ↦ ρ s 0))

/-- 任意の根族の全段が生成するイデアル。 -/
def compatibleRootFamilyIdeal (ρ : σ → ℕ → R) : Ideal R :=
  Ideal.span (Set.range (fun x : σ × ℕ ↦ ρ x.1 x.2))

omit [Fact p.Prime] in
/-- The whole root family is the supremum of its individual root ideals. -/
theorem compatibleRootFamilyIdeal_eq_iSup (ρ : σ → ℕ → R) :
    compatibleRootFamilyIdeal ρ = ⨆ s, compatibleRootIdeal (ρ s) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    exact (le_iSup (fun s => compatibleRootIdeal (ρ s)) s) Ideal.mem_span_range_self
  · apply iSup_le
    intro s
    apply Ideal.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact Ideal.subset_span ⟨(s, n), rfl⟩

/-- 最初の元のイデアルは全段の根イデアルに含まれる。 -/
theorem compatibleRootFamilyZeroIdeal_le (ρ : σ → ℕ → R) :
    compatibleRootFamilyZeroIdeal ρ ≤ compatibleRootFamilyIdeal ρ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  exact Ideal.subset_span ⟨(s, 0), rfl⟩

omit [Fact p.Prime] in
/-- 被約環への射が各最初の元を消せば、根族の全イデアルを消す。 -/
theorem compatibleRootFamilyIdeal_le_ker {T : Type v} [CommRing T] [IsReduced T]
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : R →+* T) (hf : ∀ s, f (ρ s 0) = 0) :
    compatibleRootFamilyIdeal ρ ≤ RingHom.ker f := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, n⟩, rfl⟩
  exact compatibleRootIdeal_le_ker_of_root_zero (ρ s) (hρ s) f (hf s)
    (Ideal.mem_span_range_self (x := n))

/-- 任意の根族のイデアルは冪等。一般のperfectoidイデアルの冪等性とは別。 -/
theorem compatibleRootFamilyIdeal_mul_self
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n) :
    compatibleRootFamilyIdeal ρ * compatibleRootFamilyIdeal ρ = compatibleRootFamilyIdeal ρ := by
  apply le_antisymm Ideal.mul_le_left
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, n⟩, rfl⟩
  change ρ s n ∈ compatibleRootFamilyIdeal ρ * compatibleRootFamilyIdeal ρ
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Fact.out : p.Prime).two_le
  rw [← hρ s n, hm, pow_add, pow_two]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul
    (Ideal.subset_span ⟨(s, n + 1), rfl⟩) (Ideal.subset_span ⟨(s, n + 1), rfl⟩))

/-- 完全標数p係数環では、根族イデアルはFrobeniusによる像で不変。 -/
theorem compatibleRootFamilyIdeal_map_frobenius_eq [CharP R p] [PerfectRing R p]
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n) :
    (compatibleRootFamilyIdeal ρ).map (_root_.frobeniusEquiv R p).toRingHom =
      compatibleRootFamilyIdeal ρ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    change (ρ s n) ^ p ∈ compatibleRootFamilyIdeal ρ
    have hx : ρ s n ∈ compatibleRootFamilyIdeal ρ := Ideal.subset_span ⟨(s, n), rfl⟩
    exact Ideal.pow_mem_of_mem _ hx p (Fact.out : p.Prime).pos
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    change ρ s n ∈ (compatibleRootFamilyIdeal ρ).map (_root_.frobeniusEquiv R p).toRingHom
    rw [← hρ s n]
    exact Ideal.mem_map_of_mem (_root_.frobeniusEquiv R p).toRingHom
      (Ideal.subset_span ⟨(s, n + 1), rfl⟩)

/-- 完全係数環の任意根族イデアル商は完全。零環の商も含む。 -/
theorem compatibleRootFamilyQuotient_perfectRing [CharP R p] [PerfectRing R p]
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n) :
    PerfectRing (R ⧸ compatibleRootFamilyIdeal ρ) p := by
  let K := compatibleRootFamilyIdeal ρ
  let e : R ⧸ K ≃+* R ⧸ K := Ideal.quotientEquiv K K (_root_.frobeniusEquiv R p)
    (compatibleRootFamilyIdeal_map_frobenius_eq ρ hρ).symm
  have he : ∀ x : R ⧸ K, e x = x ^ p := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk K (a ^ p) = (Ideal.Quotient.mk K a) ^ p
    rw [map_pow]
  refine ⟨?_, ?_⟩
  · intro x y h
    apply e.injective
    rw [he, he]
    exact h
  · intro x
    obtain ⟨y, hy⟩ := e.surjective x
    exact ⟨y, (he y).symm.trans hy⟩

end SerrePositivity

end CompatibleRootFamilyIdealPart

section CompatibleRootIdealFlatPart

namespace SerrePositivity
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [IsReduced R]

/-- 被約環では、一段前の根で消える元は次の根でも消える。 -/
theorem compatibleRoot_annihilator_le_succ
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) (x : R)
    (hx : ρ n * x = 0) : ρ (n + 1) * x = 0 := by
  apply eq_zero_of_pow_eq_zero (n := p)
  rw [mul_pow, hρ]
  have hp : 1 ≤ p := (Fact.out : p.Prime).pos
  have he : x ^ p = x * x ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp]
  rw [he, ← mul_assoc, hx, zero_mul]

/-- 根列の自由加群系の遷移係数は、前段の乗法核を消す。 -/
theorem compatibleRoot_transition_kills_kernel
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) (x : R)
    (hx : ρ n * x = 0) : ρ (n + 1) ^ (p - 1) * x = 0 := by
  have h := compatibleRoot_annihilator_le_succ ρ hρ n x hx
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show p - 1 ≠ 0 by omega)
  rw [hm, pow_succ, mul_assoc, h, mul_zero]

/-- 被約環における両立する根のイデアルは平坦。正則性・Noether性を要求しない。 -/
theorem compatibleRootIdeal_flat
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    Module.Flat R (compatibleRootIdeal ρ) := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hfx
  choose n hn using fun i : Fin l ↦
    (mem_compatibleRootIdeal_iff ρ hρ (x i)).mp (x i).property
  let N := Finset.univ.sup n
  have hxN : ∀ i : Fin l, ∃ b : R, (x i : R) = ρ N * b := by
    intro i
    have hle : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    have hm := compatibleRoot_principal_monotone ρ hρ hle (hn i)
    exact Ideal.mem_span_singleton.mp hm
  choose b hb using hxN
  have hval : ∑ i, f i * (x i : R) = 0 := by
    simpa using congrArg (fun y : compatibleRootIdeal ρ ↦ (y : R)) hfx
  have hker : ρ N * (∑ i, f i * b i) = 0 := by
    calc
      ρ N * (∑ i, f i * b i) = ∑ i, f i * (ρ N * b i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, f i * (x i : R) := by simp only [← hb]
      _ = 0 := hval
  let t := ρ (N + 1) ^ (p - 1)
  have ht : t * (∑ i, f i * b i) = 0 :=
    compatibleRoot_transition_kills_kernel ρ hρ N _ hker
  refine ⟨1, (fun i _ ↦ t * b i), (fun _ ↦ ⟨ρ (N + 1), Ideal.mem_span_range_self⟩), ?_, ?_⟩
  · intro i
    simp only [Fin.sum_univ_one]
    apply Subtype.ext
    change (x i : R) = (t * b i) * ρ (N + 1)
    rw [hb i, ← hρ N]
    have hp : p = (p - 1) + 1 := by have h := (Fact.out : p.Prime).pos; omega
    rw [hp, pow_succ]
    dsimp [t]
    ring
  · intro j
    calc
      ∑ i, f i * (t * b i) = t * (∑ i, f i * b i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := ht

end SerrePositivity

end CompatibleRootIdealFlatPart

section CompatibleRootIdealTensorPart

namespace SerrePositivity
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 根列の各元を、その生成するイデアルの元として扱う。 -/
def compatibleRootIdealElement (ρ : ℕ → R) (n : ℕ) : compatibleRootIdeal ρ :=
  ⟨ρ n, Ideal.mem_span_range_self⟩

/-- 根イデアルのテンソルの任意の元は、一つの根を第1成分に持つ。 -/
theorem compatibleRootIdeal_tensor_singleStage
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {C : Type u} [CommRing C] [Algebra R C] (z : compatibleRootIdeal ρ ⊗[R] C) :
    ∃ n : ℕ, ∃ c : C, z = compatibleRootIdealElement ρ n ⊗ₜ[R] c := by
  refine TensorProduct.inductionOn
    (motive := fun z ↦ ∃ n : ℕ, ∃ c : C, z = compatibleRootIdealElement ρ n ⊗ₜ[R] c)
    z (fun x c ↦ ?_) (fun x y hx hy ↦ ?_)
  · obtain ⟨n, hn⟩ := (mem_compatibleRootIdeal_iff ρ hρ x).mp x.property
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hn
    have he : x = b • compatibleRootIdealElement ρ n := by
      apply Subtype.ext
      change (x : R) = b * ρ n
      rw [hb, mul_comm]
    refine ⟨n, b • c, ?_⟩
    rw [he, TensorProduct.smul_tmul]
  · obtain ⟨n, c, hx⟩ := hx
    obtain ⟨m, d, hy⟩ := hy
    let L := max n m
    have hn : ρ n ∈ Ideal.span {ρ L} := compatibleRoot_principal_monotone ρ hρ
      (Nat.le_max_left n m) (Ideal.mem_span_singleton_self _)
    have hm : ρ m ∈ Ideal.span {ρ L} := compatibleRoot_principal_monotone ρ hρ
      (Nat.le_max_right n m) (Ideal.mem_span_singleton_self _)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hn
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hm
    have hna : compatibleRootIdealElement ρ n = a • compatibleRootIdealElement ρ L := by
      apply Subtype.ext
      change ρ n = a * ρ L
      rw [ha, mul_comm]
    have hmb : compatibleRootIdealElement ρ m = b • compatibleRootIdealElement ρ L := by
      apply Subtype.ext
      change ρ m = b * ρ L
      rw [hb, mul_comm]
    refine ⟨L, a • c + b • d, ?_⟩
    rw [hx, hy, hna, hmb, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      TensorProduct.tmul_add]

/-- 根イデアルのテンソルから終域への、包含と乗法により定まる線形射。 -/
def compatibleRootIdealTensorMap (ρ : ℕ → R) (C : Type u) [CommRing C] [Algebra R C] :
    compatibleRootIdeal ρ ⊗[R] C →ₗ[R] C :=
  (TensorProduct.lid R C).toLinearMap ∘ₗ ((compatibleRootIdeal ρ).subtype.rTensor C)

/-- テンソル射の純粋テンソル上の式。 -/
@[simp] theorem compatibleRootIdealTensorMap_tmul
    (ρ : ℕ → R) (C : Type u) [CommRing C] [Algebra R C]
    (x : compatibleRootIdeal ρ) (c : C) :
    compatibleRootIdealTensorMap ρ C (x ⊗ₜ[R] c) = (x : R) • c := rfl

/-- 被約な終域では、根イデアルのテンソルから終域への標準射は単射。
終域の正則性・平坦性を仮定しない。 -/
theorem compatibleRootIdealTensorMap_injective
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (C : Type u) [CommRing C] [Algebra R C] [IsReduced C] :
    Function.Injective (compatibleRootIdealTensorMap ρ C) := by
  have hzero : ∀ z : compatibleRootIdeal ρ ⊗[R] C,
      compatibleRootIdealTensorMap ρ C z = 0 → z = 0 := by
    intro z hz
    obtain ⟨n, c, rfl⟩ := compatibleRootIdeal_tensor_singleStage ρ hρ z
    have hmul : algebraMap R C (ρ n) * c = 0 := by
      simpa only [compatibleRootIdealTensorMap_tmul, compatibleRootIdealElement,
        Algebra.smul_def] using hz
    have hρC : ∀ m, (algebraMap R C (ρ (m + 1))) ^ p = algebraMap R C (ρ m) := by
      intro m
      rw [← map_pow, hρ]
    have hkill := compatibleRoot_transition_kills_kernel
      (fun m ↦ algebraMap R C (ρ m)) hρC n c hmul
    have he : compatibleRootIdealElement ρ n =
        ρ (n + 1) ^ (p - 1) • compatibleRootIdealElement ρ (n + 1) := by
      apply Subtype.ext
      change ρ n = ρ (n + 1) ^ (p - 1) * ρ (n + 1)
      rw [← hρ n, ← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).pos]
    rw [he, TensorProduct.smul_tmul]
    have hs : ρ (n + 1) ^ (p - 1) • c = 0 := by
      rw [Algebra.smul_def, map_pow]
      exact hkill
    rw [hs, TensorProduct.tmul_zero]
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hxy, sub_self]

end SerrePositivity

end CompatibleRootIdealTensorPart

section CompatibleRootPerfectQuotientPart

namespace SerrePositivity
variable {p : ℕ} [Fact p.Prime] {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]

/-- 両立する根のイデアルはFrobeniusによる像で不変。 -/
theorem compatibleRootIdeal_map_frobenius_eq
    (ρ : ℕ → k) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    (compatibleRootIdeal ρ).map (_root_.frobeniusEquiv k p).toRingHom =
      compatibleRootIdeal ρ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change (ρ n) ^ p ∈ compatibleRootIdeal ρ
    exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_range_self) p (Fact.out : p.Prime).pos
  · apply Ideal.span_le.mpr
    rintro _ ⟨n, rfl⟩
    rw [← hρ n]
    exact Ideal.mem_map_of_mem (_root_.frobeniusEquiv k p).toRingHom
      (Ideal.mem_span_range_self (x := n + 1))

/-- 完全係数環の根イデアル商は完全。商のCharPを要求せず、零環も含む。 -/
theorem compatibleRootQuotient_perfectRing
    (ρ : ℕ → k) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    PerfectRing (k ⧸ compatibleRootIdeal ρ) p := by
  let K := compatibleRootIdeal ρ
  let e : k ⧸ K ≃+* k ⧸ K := Ideal.quotientEquiv K K (_root_.frobeniusEquiv k p)
    (compatibleRootIdeal_map_frobenius_eq ρ hρ).symm
  have he : ∀ x : k ⧸ K, e x = x ^ p := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk K (a ^ p) = (Ideal.Quotient.mk K a) ^ p
    rw [map_pow]
  refine ⟨?_, ?_⟩
  · intro x y h
    apply e.injective
    rw [he, he]
    exact h
  · intro x
    obtain ⟨y, hy⟩ := e.surjective x
    exact ⟨y, (he y).symm.trans hy⟩

end SerrePositivity

end CompatibleRootPerfectQuotientPart
