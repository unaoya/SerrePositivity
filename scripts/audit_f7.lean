-- lake build の後、lake env lean scripts/audit_f7.lean で実行する。
import SerrePositivity.CommutativeAlgebra.PerfectoidFontaineSeparation
import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientFontaineIso
import Mathlib.Util.AssertNoSorry

open SerrePositivity
universe u

-- BS F7の正確な仮定だけで核進分離性を供給する。
theorem f7_audit_bs_signature (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]
    (hS : IsIntegralPerfectoid S p)
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x)) :
    IsHausdorff (RingHom.ker (WittVector.fontaineTheta S p))
      (WittVector p (PreTilt S p)) :=
  hS.fontaine_kernel_isHausdorff S p hregular

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

-- 既存の条件付き全射判定へF7を適用し、標的の核進分離性を導出する。
theorem f7_audit_fontaine_comparison_surjective
    [IsPrecomplete (Ideal.span {d}) (WittVector p k)]
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    Function.Surjective (wittQuotientFontaineMap p k d) := by
  have := (wittRegularQuotient_isIntegralPerfectoid p k d hd hreg).fontaine_kernel_isHausdorff
    (WittVector p k ⧸ Ideal.span {d}) p
    (wittQuotient_p_mul_injective_of_coeff_zero_regular p k d hreg)
  exact wittRegularQuotientFontaineMap_surjective p k d hd hreg

-- 源のd進完備性を残したまま、台環比較の全単射性も接続できる。
theorem f7_audit_fontaine_comparison_bijective
    [IsAdicComplete (Ideal.span {d}) (WittVector p k)]
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    Function.Bijective (wittQuotientFontaineMap p k d) := by
  have := (wittRegularQuotient_isIntegralPerfectoid p k d hd hreg).fontaine_kernel_isHausdorff
    (WittVector p k ⧸ Ideal.span {d}) p
    (wittQuotient_p_mul_injective_of_coeff_zero_regular p k d hreg)
  exact wittRegularQuotientFontaineMap_bijective p k d hd hreg

end SerrePositivity.BhattScholze

assert_no_sorry f7_audit_bs_signature
assert_no_sorry SerrePositivity.BhattScholze.f7_audit_fontaine_comparison_surjective
assert_no_sorry SerrePositivity.BhattScholze.f7_audit_fontaine_comparison_bijective
