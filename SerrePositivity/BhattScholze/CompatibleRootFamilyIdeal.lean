module

public import SerrePositivity.BhattScholze.CompatibleRootIdeal
public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # B4-4：任意の根族が生成するイデアル

有限生成を仮定せず、各生成元の両立する根を同時に扱う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type u}

/-- 根族の最初の元の全体が生成するイデアル。 -/
def compatibleRootFamilyZeroIdeal (ρ : σ → ℕ → R) : Ideal R :=
  Ideal.span (Set.range (fun s ↦ ρ s 0))

/-- 任意の根族の全段が生成するイデアル。 -/
def compatibleRootFamilyIdeal (ρ : σ → ℕ → R) : Ideal R :=
  Ideal.span (Set.range (fun x : σ × ℕ ↦ ρ x.1 x.2))

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

end SerrePositivity.BhattScholze
