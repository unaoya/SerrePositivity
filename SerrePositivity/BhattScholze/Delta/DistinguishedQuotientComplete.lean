module

public import SerrePositivity.BhattScholze.Delta.DistinguishedPowerTorsion
public import SerrePositivity.CommutativeAlgebra.AdicBoundedTorsionQuotient

/-! # 完全p進完備δ環のdistinguished商と冪商のp完備性

受領したF5に既存BS Lemma 2.34の有界ねじれ評価を供給する。
商のp正則性・Noether性・有限表示性を仮定しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全p進完備δ環のdistinguished商は、pねじれを許して古典的p進完備。 -/
theorem IsPerfect.distinguished_quotient_isAdicComplete {D : DeltaStructure p A}
    (hD : D.IsPerfect) [IsAdicComplete (Ideal.span {(p : A)}) A] {d : A}
    (hd : D.IsDistinguished d) :
    IsAdicComplete (Ideal.span {(p : A ⧸ Ideal.span {d})}) (A ⧸ Ideal.span {d}) := by
  apply isAdicComplete_principal_quotient_natCast_of_bounded_torsion A p d
  refine ⟨1, fun n x hx ↦ ?_⟩
  simpa only [pow_one] using hD.distinguished_quotient_p_pow_torsion_killed_by_p hd n x hx

/-- distinguished元の全冪商は古典的p進完備。零冪商も含む。 -/
theorem IsPerfect.distinguished_power_quotient_isAdicComplete {D : DeltaStructure p A}
    (hD : D.IsPerfect) [IsAdicComplete (Ideal.span {(p : A)}) A] {d : A}
    (hd : D.IsDistinguished d) (k : ℕ) :
    IsAdicComplete (Ideal.span {(p : A ⧸ Ideal.span {d ^ k})}) (A ⧸ Ideal.span {d ^ k}) := by
  apply isAdicComplete_principal_power_quotient_natCast_of_bounded_torsion A p d k
  exact ⟨k, fun n x hx ↦ hD.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow hd k n x hx⟩

end SerrePositivity.BhattScholze.DeltaStructure
