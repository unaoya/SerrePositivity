module

public import SerrePositivity.CommutativeAlgebra.FrobeniusRootKernels
public import Mathlib.RingTheory.Perfection

/-! # 成分ごとの割り算からperfectionの第0射影の核を生成する

商の選択の誤差がFrobeniusで消える場合、商を一段先で選んでp乗すれば
両立する列になる。perfectoid性やFontaine核の単項性は仮定しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- 各成分の割り算を両立する商の列へまとめる。
正の段で生成元の零化元がFrobeniusで消えることが、選択の誤差を除く。 -/
theorem perfection_dvd_of_coeff_dvd_of_annihilator (d x : Perfection R p)
    (hdiv : ∀ n, Perfection.coeff R p n d ∣ Perfection.coeff R p n x)
    (hann : ∀ n z, Perfection.coeff R p (n + 1) d * z = 0 → z ^ p = 0) : d ∣ x := by
  choose a ha using hdiv
  have herr (n : ℕ) :
      Perfection.coeff R p n d * (a n - a (n + 1) ^ p) = 0 := by
    rw [mul_sub, ← ha n, ← Perfection.coeff_pow_p' d n, ← mul_pow,
      ← ha (n + 1), Perfection.coeff_pow_p', sub_self]
  have hcompat (n : ℕ) : (a (n + 2) ^ p) ^ p = a (n + 1) ^ p := by
    have h := hann n (a (n + 1) - a (n + 2) ^ p) (herr (n + 1))
    rw [sub_pow_char, sub_eq_zero] at h
    exact h.symm
  let b : Perfection R p := ⟨fun n ↦ a (n + 1) ^ p, hcompat⟩
  refine ⟨b, ?_⟩
  apply Perfection.ext
  intro n
  change Perfection.coeff R p n x =
    Perfection.coeff R p n d * a (n + 1) ^ p
  rw [← Perfection.coeff_pow_p' d n, ← mul_pow, ← ha (n + 1),
    Perfection.coeff_pow_p']

/-- 最初のFrobenius核と零化元の条件から、第0射影の核を主イデアルとして計算する。 -/
theorem perfection_coeff_zero_kernel_eq_span
    (hF : Function.Surjective (frobenius R p)) (d : Perfection R p)
    (hd0 : Perfection.coeff R p 0 d = 0)
    (hker : ∀ z : R, z ^ p = 0 ↔ z ∈ Ideal.span {Perfection.coeff R p 1 d})
    (hann : ∀ n z, Perfection.coeff R p (n + 1) d * z = 0 → z ^ p = 0) :
    RingHom.ker (Perfection.coeff R p 0) = Ideal.span {d} := by
  apply le_antisymm
  · intro x hx
    apply Ideal.mem_span_singleton.mpr
    apply perfection_dvd_of_coeff_dvd_of_annihilator R p d x _ hann
    intro n
    apply Ideal.mem_span_singleton.mp
    apply (frobenius_pow_kernel_iff_mem_span R p hF
      (fun k ↦ Perfection.coeff R p k d) hd0
      (fun k ↦ Perfection.coeff_pow_p' d k) hker n _).mp
    have h := compatibleRoots_pow p (fun k ↦ Perfection.coeff R p k x)
      (fun k ↦ Perfection.coeff_pow_p' x k) 0 n
    simpa only [Nat.zero_add, show Perfection.coeff R p 0 x = 0 from hx] using h
  · exact (Ideal.span_singleton_le_iff_mem _).mpr hd0

end SerrePositivity
