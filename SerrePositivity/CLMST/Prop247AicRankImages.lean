module

public import SerrePositivity.CommutativeAlgebra.RankLocus
public import SerrePositivity.CommutativeAlgebra.ReducedSpectrum
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedPerfectoidQuotient
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationIdentity

/-! # Prop 2.4.7：André 基底上の実 rank 像は既に perfectoid

元の rank 開集合を D(d) と表し、その切断への像を R/Ann(d) と同定する。
絶対整閉 perfectoid 環の既存の annihilator 商定理を適用する。
Cor 8.12 と一般整代数の perfectoid 化の存在引用は使用しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false

/-- André 基底上では各元の Ri 自身が perfectoid である。 -/
theorem prop247_aic_rankImage_isIntegralPerfectoid
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    IsIntegralPerfectoid (openSectionImage R (rankOpen R S g hetale n)) p := by
  letI := hR.isReduced R p
  obtain ⟨a, ha⟩ := rankOpen_exists_basicOpen R S g hetale n
  have hI : PrimeSpectrum.vanishingIdeal
      (rankOpen R S g hetale n : Set (PrimeSpectrum R)) =
      (Ideal.span {g * a}).annihilator := by
    rw [ha]
    exact vanishingIdeal_basicOpen_eq_annihilator R (g * a)
  let e := (Ideal.quotientEquivAlgOfEq R hI.symm).trans
    (openSectionImageQuotientEquiv R (rankOpen R S g hetale n))
  exact BhattScholze.isIntegralPerfectoid_of_ringEquiv p e.toRingEquiv
    (aicPerfectoid_annihilatorPrincipalQuotient R p hR hAIC (g * a))

/-- 各 Ri の指定 perfectoid 化単位そのものが全単射である。 -/
theorem prop247_aic_rankTarget_unit_bijective
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T]
    (f : openSectionImage R (rankOpen R S g hetale n) →+* T)
    (hf : IsPerfectoidization p f) : Function.Bijective f := by
  have hI := prop247_aic_rankImage_isIntegralPerfectoid R S p hR hAIC g hetale n
  obtain ⟨e, he⟩ := hI.isPerfectoidization_id.exists_equiv p hf
  have he' : e.toRingHom = f := by simpa only [RingHom.comp_id] using he
  rw [← he']
  exact e.bijective

end SerrePositivity.CLMST
