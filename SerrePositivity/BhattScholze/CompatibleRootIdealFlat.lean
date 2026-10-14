module

public import SerrePositivity.BhattScholze.CompatibleRootIdeal
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # B4-5：被約環の根イデアルの平坦性

BS17著者版Lemma 3.16（https://people.mpim-bonn.mpg.de/scholze/Witt.pdf、p.13）の
根イデアルの計算を、Mathlibの平坦性の方程式判定へ直接接続する。
Tor独立性全体や完備テンソルのperfectoid性はこの定理の結論に含めない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
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

end SerrePositivity.BhattScholze
