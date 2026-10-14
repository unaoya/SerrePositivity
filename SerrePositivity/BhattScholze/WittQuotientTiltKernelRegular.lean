module

public import SerrePositivity.BhattScholze.WittQuotientTiltMap
public import Mathlib.Algebra.Regular.Basic

/-! # 第0Witt係数が正則な商のtilt射影核

kでd₀が非零因子という仮定を明示する。一般のpねじれを持つWitt商へ
この仮定を無条件に適用しない。互換商の列は共通PerfectionPrincipalKernelを使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- d₀が正則なら、tilt核候補の正の座標の零化元はFrobeniusで消える。 -/
theorem wittQuotientTilt_annihilator_pow_eq_zero
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) (n : ℕ)
    (z : ModP (WittVector p k ⧸ Ideal.span {d}) p)
    (hz : PreTilt.coeff (n + 1) (wittQuotientTiltMap p k d (d.coeff 0)) * z = 0) :
    z ^ p = 0 := by
  let e := wittQuotientModPEquiv p k d
  let q := Ideal.Quotient.mk (Ideal.span {d.coeff 0})
  let a := ((_root_.frobeniusEquiv k p).symm : k → k)^[n + 1] (d.coeff 0)
  let N := p ^ (n + 1)
  have he (x : k) : e (wittQuotientCoefficientMap p k d x) = q x := by
    change e (e.symm (q x)) = q x
    exact e.apply_symm_apply _
  have ha : a ^ N = d.coeff 0 := iterate_frobeniusEquiv_symm_pow_p_pow k p _ (n + 1)
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hN : 2 ≤ N := by
    exact hp2.trans (Nat.le_self_pow (by omega : n + 1 ≠ 0) p)
  have haReg : IsLeftRegular a :=
    (IsLeftRegular.pow_iff (by omega : 0 < N)).mp (by rw [ha]; exact hreg)
  obtain ⟨b, hb⟩ := wittQuotientCoefficientMap_surjective p k d z
  have hprod : a * b ∈ Ideal.span {d.coeff 0} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (a * b) = 0
    have h := congrArg e hz
    rw [wittQuotientTiltMap_coeff, ← hb] at h
    change e (wittQuotientCoefficientMap p k d a * wittQuotientCoefficientMap p k d b) = e 0 at h
    rw [map_mul, he, he, map_zero] at h
    simpa only [map_mul] using h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hprod
  have hN' : N - 1 + 1 = N := by omega
  have hb' : b = a ^ (N - 1) * c := by
    apply haReg
    change a * b = a * (a ^ (N - 1) * c)
    have hpow : a ^ N = a * a ^ (N - 1) := by
      calc
        a ^ N = a ^ (N - 1 + 1) := congrArg (fun m ↦ a ^ m) hN'.symm
        _ = a * a ^ (N - 1) := pow_succ' _ _
    rw [hc, ← ha, hpow, mul_assoc]
  have hle : N ≤ (N - 1) * p := by
    have h := Nat.mul_le_mul_left (N - 1) hp2
    omega
  have hbpow : b ^ p ∈ Ideal.span {d.coeff 0} := by
    rw [hb', mul_pow, ← pow_mul]
    apply (Ideal.span {d.coeff 0}).mul_mem_right
    apply (Ideal.span {d.coeff 0}).pow_mem_of_pow_mem (m := N) _ hle
    rw [ha]
    exact Ideal.subset_span (by simp)
  apply e.injective
  rw [map_pow, ← hb, he]
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hbpow, map_zero]

/-- d₀が正則なWitt商のtiltの第0射影核は、d₀の標準tilt像で生成される。 -/
theorem wittQuotientTilt_coeff_zero_kernel_eq_span
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    RingHom.ker (PreTilt.coeff 0 : PreTilt (WittVector p k ⧸ Ideal.span {d}) p →+*
      ModP (WittVector p k ⧸ Ideal.span {d}) p) =
        Ideal.span {wittQuotientTiltMap p k d (d.coeff 0)} := by
  apply perfection_coeff_zero_kernel_eq_span
    (ModP (WittVector p k ⧸ Ideal.span {d}) p) p
    ((wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d}))
    (wittQuotientTiltMap p k d (d.coeff 0)) (wittQuotientTiltMap_coeff_zero_d p k d)
  · intro z
    change z ^ p = 0 ↔ z ∈ Ideal.span {(PreTilt.coeff 1
      (wittQuotientTiltMap p k d (d.coeff 0)))}
    rw [wittQuotientTiltMap_coeff, wittQuotientCoefficientMap_apply]
    apply wittQuotientModP_pow_eq_zero_iff_mem_span
    exact frobeniusEquiv_symm_pow_p k p _
  · exact wittQuotientTilt_annihilator_pow_eq_zero p k d hreg

end SerrePositivity.BhattScholze
