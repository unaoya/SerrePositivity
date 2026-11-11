module

public import Mathlib.RingTheory.DividedPowers.Padic
public import Mathlib.RingTheory.DividedPowers.DPMorphism

/-!
# イデアルの生成元による分冪の制限

## 概要
単射に沿って分冪を制限するとき、正次数の分冪が元のイデアルに入る条件を
イデアルの生成元で確かめる。

## 方針
分冪の加法とスカラー倍の公式を使い、イデアルの生成で帰納する。
構造そのものには Mathlib の `DividedPowers.ofInjective` を用いる。

## 規約
係数環の正則性は環射の単射性にまとめる。

## 使われ方
Berthelot I.2.3.1 の多項式の分冪包を、階乗分母を用いて表示する。
-/

public noncomputable section

namespace SerrePositivity.BhattScholze.Prismatic

open Ideal

variable {R E : Type*} [CommSemiring R] [CommSemiring E] (f : R →+* E) (S : Set R)
variable (δ : DividedPowers ((span S).map f))
variable (hlift : ∀ x ∈ S, ∀ n : ℕ, n ≠ 0 →
  ∃ y ∈ span S, f y = δ.dpow n (f x))

include hlift in
private theorem lift_dpow_span {x : R} (hx : x ∈ span S) (n : ℕ) :
    ∃ (y : R) (_ : n ≠ 0 → y ∈ span S), f y = δ.dpow n (f x) := by
  induction hx using Submodule.span_induction generalizing n with
  | mem x hx =>
    by_cases hn : n = 0
    · subst n
      exact ⟨1, fun h => (h rfl).elim,
        (map_one f).trans (δ.dpow_zero (mem_map_of_mem f (subset_span hx))).symm⟩
    · obtain ⟨y, hy, hy'⟩ := hlift x hx n hn
      exact ⟨y, fun _ => hy, hy'⟩
  | zero =>
    by_cases hn : n = 0
    · subst n
      refine ⟨1, fun h => (h rfl).elim, ?_⟩
      rw [map_one, map_zero, δ.dpow_zero (Ideal.zero_mem _)]
    · refine ⟨0, fun _ => Ideal.zero_mem _, ?_⟩
      rw [map_zero, δ.dpow_eval_zero hn]
  | add x y hx hy ihx ihy =>
    choose a ha ha' using ihx
    choose b hb hb' using ihy
    refine ⟨∑ i ∈ Finset.antidiagonal n, a i.1 * b i.2, ?_, ?_⟩
    · intro hn
      apply (span S).sum_mem
      intro i hi
      by_cases h : i.1 = 0
      · apply (span S).mul_mem_left
        apply hb
        intro h'
        exact hn (by simpa only [h, h', add_zero] using (Finset.mem_antidiagonal.mp hi).symm)
      · exact (span S).mul_mem_right _ (ha _ h)
    · rw [map_add, δ.dpow_add (mem_map_of_mem f hx) (mem_map_of_mem f hy), map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, ha', hb']
  | smul r x hx ih =>
    obtain ⟨y, hy, hy'⟩ := ih n
    refine ⟨r ^ n * y, fun hn => (span S).mul_mem_left _ (hy hn), ?_⟩
    rw [smul_eq_mul, map_mul, map_pow, hy', map_mul, δ.dpow_mul (mem_map_of_mem f hx)]

/-- 生成元の正次数の分冪が持ち上がれば、イデアル全体へ分冪を制限できる。 -/
def dividedPowersOfInjectiveSpan (hf : Function.Injective f) : DividedPowers (span S) :=
  DividedPowers.ofInjective _ _ f hf δ rfl fun n _ hx => lift_dpow_span f S δ hlift hx n

/-- 制限した分冪は標的環の分冪に一致する。 -/
theorem dividedPowersOfInjectiveSpan_isDPMorphism (hf : Function.Injective f) :
    (dividedPowersOfInjectiveSpan f S δ hlift hf).IsDPMorphism δ f := by
  refine ⟨le_rfl, fun {n} x hx => ?_⟩
  classical
  change δ.dpow n (f x) =
    f (if hx : x ∈ span S then (lift_dpow_span f S δ hlift hx n).choose else 0)
  rw [dite_eq_left hx]
  exact (lift_dpow_span f S δ hlift hx n).choose_spec.choose_spec.symm

end SerrePositivity.BhattScholze.Prismatic
