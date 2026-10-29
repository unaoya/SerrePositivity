module

public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import SerrePositivity.CommutativeAlgebra.AdicRecurrence

/-! # 主元進の完備性と有界ねじれ

概要：元 `a ∈ R` について
- `a` で割った商の上で正則な元 `x` の整除性（`x y ∈ (a^n)` から `y ∈ (a^n)`）。
- `M` が `a` 進完備で `x` が `M/aM` 上正則なら、`M/xM` も `a` 進完備で `x` は正則。
- 有界な `a` 冪ねじれを持つ加群では、漸化式の写像（`AdicRecurrence`）の単射性・全単射性から分離性・完備性。
方針：`a` 進の合同を一段ずつ持ち上げる。ねじれの上界で漸化式の解を比較する。
規約：完備性は古典的。導来完備性との比較は `Adic/BoundedTorsionQuotient`。
使われ方：導来完備化（HomologicalAlgebra）、Bhatt–Scholze 側の distinguished な元。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section AdicRegularQuotient

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]

theorem dvd_of_mul_dvd_of_regular_mod (a g : R)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g))
    (x : R) (hx : a ∣ g * x) : a ∣ x := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hg
  change Ideal.Quotient.mk (Ideal.span {a}) g * Ideal.Quotient.mk (Ideal.span {a}) x =
    Ideal.Quotient.mk (Ideal.span {a}) g * 0
  rw [← map_mul, mul_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hx)

theorem pow_dvd_of_mul_dvd_of_regular_mod (a g : R) (ha : IsSMulRegular R a)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g))
    (n : ℕ) (x : R) (hx : a ^ n ∣ g * x) : a ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, hy⟩ := dvd_of_mul_dvd_of_regular_mod R a g hg x
      ((dvd_pow_self a (Nat.succ_ne_zero n)).trans hx)
    obtain ⟨z, hz⟩ := hx
    have hcancel : g * y = a ^ n * z := by
      apply ha
      change a * (g * y) = a * (a ^ n * z)
      calc
        _ = g * x := by rw [hy]; ring
        _ = a ^ (n + 1) * z := hz
        _ = _ := by rw [pow_succ]; ring
    obtain ⟨w, hw⟩ := ih y ⟨z, hcancel⟩
    exact ⟨w, by rw [hy, hw, pow_succ]; ring⟩

theorem isSMulRegular_quotient_span_of_regular_mod (a g : R) (ha : IsSMulRegular R a)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g)) :
    IsSMulRegular (R ⧸ Ideal.span {g}) (Ideal.Quotient.mk (Ideal.span {g}) a) := by
  change IsSMulRegular (R ⧸ Ideal.span {g}) (algebraMap R (R ⧸ Ideal.span {g}) a)
  rw [isSMulRegular_algebraMap_iff]
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {g}) a).mpr
  intro x hx
  change a * x ∈ Ideal.span {g} at hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨z, hz⟩ := dvd_of_mul_dvd_of_regular_mod R a g hg y ⟨x, hy.symm⟩
  apply Ideal.mem_span_singleton.mpr
  refine ⟨z, ?_⟩
  apply ha
  change a * x = a * (g * z)
  rw [hy, hz]
  ring

theorem isAdicComplete_quotient_span_of_regular_mod (a g : R)
    [IsAdicComplete (Ideal.span {a}) R] (ha : IsSMulRegular R a)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g)) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a}) (R ⧸ Ideal.span {g}) := by
  let f := LinearMap.mulLeft R g
  have hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f ((Ideal.span {a}) ^ (n + k) • (⊤ : Submodule R R)) ≤
        (Ideal.span {a}) ^ n • (⊤ : Submodule R R) := by
    refine ⟨0, fun n x hx ↦ ?_⟩
    simp only [Submodule.mem_comap, f, LinearMap.mulLeft_apply, Nat.add_zero,
      Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
    exact pow_dvd_of_mul_dvd_of_regular_mod R a g ha hg n x hx
  have hrange : f.range = (Ideal.span {g} : Submodule R R) := by
    ext x
    simp only [LinearMap.mem_range, f, LinearMap.mulLeft_apply, Ideal.mem_span_singleton, dvd_def]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩
  let : IsAdicComplete (Ideal.span {a}) (R ⧸ Ideal.span {g}) := by
    rw [← hrange]
    exact isAdicComplete_quotient_range_of_uniform_filtration_bound (Ideal.span {a}) f hbound
  have hmap : (Ideal.span {a}).map (algebraMap R (R ⧸ Ideal.span {g})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance

end AdicRegularQuotient

section AdicBoundedTorsion

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 有界なf冪ねじれの下では、差分作用の単射性からf進分離性が従う。 -/
theorem isHausdorff_of_adicRecurrenceMap_injective_of_bounded_torsion (f : R)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ N • x = 0)
    (hinj : Function.Injective (adicRecurrenceMap (M := M) f)) :
    IsHausdorff (Ideal.span {f}) M := by
  classical
  obtain ⟨N, hN⟩ := hbounded
  constructor
  intro x hx
  have hdiv (n : ℕ) : ∃ y : M, f ^ n • y = x := by
    apply (mem_principal_pow_smul_top f n x).mp
    simpa only [sub_zero] using SModEq.sub_mem.mp (hx n)
  choose y hy using hdiv
  let z : ℕ → M := fun n ↦ f ^ N • y (n + N)
  have hstep (n : ℕ) : z n = f • z (n + 1) := by
    have herr : f ^ (n + N) • (y (n + N) - f • y (n + 1 + N)) = 0 := by
      rw [smul_sub, ← mul_smul, ← pow_succ, hy]
      have he : n + N + 1 = n + 1 + N := by omega
      rw [he, hy, sub_self]
    have h := hN (n + N) _ herr
    dsimp only [z]
    rw [smul_sub, smul_smul, mul_comm (f ^ N) f, ← smul_smul] at h
    exact sub_eq_zero.mp h
  have hz : adicRecurrenceMap f z = 0 := by
    ext n
    exact sub_eq_zero.mpr (hstep n)
  have hzero : z = 0 := hinj (hz.trans (map_zero _).symm)
  have hxz : z 0 = x := by simpa only [z, zero_add] using hy N
  rw [hzero] at hxz
  exact hxz.symm

/-- 有界ねじれの下で、差分作用の全単射性から古典的完備性が従う。 -/
theorem isAdicComplete_of_adicRecurrenceMap_bijective_of_bounded_torsion (f : R)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ N • x = 0)
    (hbij : Function.Bijective (adicRecurrenceMap (M := M) f)) :
    IsAdicComplete (Ideal.span {f}) M := by
  let := isHausdorff_of_adicRecurrenceMap_injective_of_bounded_torsion f hbounded hbij.1
  let := isPrecomplete_of_adicRecurrenceMap_surjective f hbij.2
  exact ⟨⟩

end AdicBoundedTorsion

end SerrePositivity
