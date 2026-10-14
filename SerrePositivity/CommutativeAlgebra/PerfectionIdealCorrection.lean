module

public import Mathlib.RingTheory.Perfection

/-! # イデアル内の根による互換列の誤差の補正 -/

@[expose] public noncomputable section
namespace SerrePositivity
variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- p乗根を取れるイデアル内に列の誤差があれば、イデアル内の補正で互換列になる。 -/
theorem exists_perfection_of_errors_in_ideal (J : Ideal R)
    (hroots : ∀ u : J, ∃ v : J, (v : R) ^ p = u)
    (c : ℕ → R) (herr : ∀ n, c n - c (n + 1) ^ p ∈ J) :
    ∃ b : Perfection R p, ∀ n, Perfection.coeff R p n b - c n ∈ J := by
  let step (n : ℕ) (u : J) : J := Classical.choose
    (hroots ⟨c n - c (n + 1) ^ p + u, J.add_mem (herr n) u.property⟩)
  let u : ℕ → J := fun n ↦ Nat.rec 0 step n
  have hu (n : ℕ) : (u (n + 1)).val ^ p = c n - c (n + 1) ^ p + (u n).val := by
    exact Classical.choose_spec
      (hroots ⟨c n - c (n + 1) ^ p + (u n).val, J.add_mem (herr n) (u n).property⟩)
  have hb (n : ℕ) : (c (n + 1) + (u (n + 1)).val) ^ p = c n + (u n).val := by
    rw [add_pow_char, hu]
    ring
  refine ⟨⟨fun n ↦ c n + (u n).val, hb⟩, ?_⟩
  intro n
  change c n + (u n).val - c n ∈ J
  simpa only [add_sub_cancel_left] using (u n).property

/-- 座標の零化元のp乗が根を持つイデアルに入り、そのイデアルを生成元が零化すれば、
座標ごとの商を補正してperfection上の商を得る。 -/
theorem perfection_dvd_of_coeff_dvd_of_ideal_correction
    (d x : Perfection R p) (J : Ideal R)
    (hroots : ∀ u : J, ∃ v : J, (v : R) ^ p = u)
    (hkill : ∀ n z, z ∈ J → Perfection.coeff R p n d * z = 0)
    (hdiv : ∀ n, Perfection.coeff R p n d ∣ Perfection.coeff R p n x)
    (hann : ∀ n z, Perfection.coeff R p (n + 1) d * z = 0 → z ^ p ∈ J) : d ∣ x := by
  choose a ha using hdiv
  have herr (n : ℕ) :
      Perfection.coeff R p n d * (a n - a (n + 1) ^ p) = 0 := by
    rw [mul_sub, ← ha n, ← Perfection.coeff_pow_p' d n, ← mul_pow,
      ← ha (n + 1), Perfection.coeff_pow_p', sub_self]
  let c : ℕ → R := fun n ↦ a (n + 1) ^ p
  have hc (n : ℕ) : c n - c (n + 1) ^ p ∈ J := by
    have h := hann n (a (n + 1) - a (n + 2) ^ p) (herr (n + 1))
    rw [sub_pow_char] at h
    exact h
  obtain ⟨b, hb⟩ := exists_perfection_of_errors_in_ideal R p J hroots c hc
  refine ⟨b, ?_⟩
  apply Perfection.ext
  intro n
  have hz := hkill n _ (hb n)
  rw [mul_sub, sub_eq_zero] at hz
  change Perfection.coeff R p n x = Perfection.coeff R p n d * Perfection.coeff R p n b
  rw [hz]
  change Perfection.coeff R p n x = Perfection.coeff R p n d * a (n + 1) ^ p
  rw [← Perfection.coeff_pow_p' d n, ← mul_pow, ← ha (n + 1), Perfection.coeff_pow_p']

end SerrePositivity
