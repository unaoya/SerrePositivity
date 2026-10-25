-- lake build の後、lake env lean scripts/audit_f5.lean で実行する。
import SerrePositivity.CommutativeAlgebra.AdicBoundedTorsionQuotient
import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedPowerTorsion
import Mathlib.Util.AssertNoSorry

open SerrePositivity SerrePositivity.DerivedCompletion CategoryTheory
universe u

-- 有界指数が0の場合：ねじれのない加群。正則性を別仮定として渡さない。
theorem f5_audit_zero_bound (R : Type u) [CommRing R] (f : R) (M : ModuleCat.{u} R)
    (hM : IsModuleComplete R f M)
    (h0 : ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → x = 0) :
    IsAdicComplete (Ideal.span {f}) M := by
  apply isAdicComplete_of_isModuleComplete_of_bounded_torsion R f M hM
  exact ⟨0, fun n x hx ↦ by simpa using h0 n x hx⟩

-- f=0を除外しないことを確認する。
theorem f5_audit_zero_scalar (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    IsHausdorff (Ideal.span {(0 : R)}) M := by
  apply isHausdorff_of_adicRecurrenceMap_injective_of_bounded_torsion (0 : R)
  · exact ⟨1, fun _ _ _ ↦ by simp⟩
  · intro x y h
    simpa only [adicRecurrenceMap, LinearMap.coe_mk, AddHom.coe_mk,
      zero_smul, sub_zero] using h

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]

-- 既存BS Lemma 2.34のN=1を、完備性を結論するF5へそのまま渡す。
theorem f5_audit_distinguished_quotient (D : DeltaStructure p A) (hD : D.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] {d : A} (hd : D.IsDistinguished d) :
    IsAdicComplete (Ideal.span {(p : A ⧸ Ideal.span {d})}) (A ⧸ Ideal.span {d}) := by
  apply isAdicComplete_regular_quotient_natCast_of_bounded_torsion A p d
    hD.p_mul_injective (hD.distinguished_mul_injective hd)
  refine ⟨1, fun n x hx ↦ ?_⟩
  simpa only [pow_one] using hD.distinguished_quotient_p_pow_torsion_killed_by_p hd n x hx

-- 既存のd冪商の有界指数kを渡す。k=0の零環も含む。
theorem f5_audit_distinguished_power_quotient (D : DeltaStructure p A) (hD : D.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] {d : A} (hd : D.IsDistinguished d)
    (k : ℕ) :
    IsAdicComplete (Ideal.span {(p : A ⧸ Ideal.span {d ^ k})})
      (A ⧸ Ideal.span {d ^ k}) := by
  apply isAdicComplete_principal_power_quotient_natCast_of_bounded_torsion A p d k
  exact ⟨k, fun n x hx ↦ hD.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow hd k n x hx⟩

end SerrePositivity.BhattScholze.DeltaStructure

assert_no_sorry f5_audit_zero_bound
assert_no_sorry f5_audit_zero_scalar
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.f5_audit_distinguished_quotient
assert_no_sorry SerrePositivity.BhattScholze.DeltaStructure.f5_audit_distinguished_power_quotient
