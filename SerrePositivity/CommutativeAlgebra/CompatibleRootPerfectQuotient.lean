module

public import SerrePositivity.CommutativeAlgebra.CompatibleRootIdeal
public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # 完全標数p環の根イデアル商

両立する根の全体で割るとFrobeniusは同型になる。零環の商も含む。
一般混標数環の根イデアル商のperfectoid性とは区別する。
-/

@[expose] public noncomputable section
universe u
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
