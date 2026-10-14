module

public import SerrePositivity.BhattScholze.WittCompleteQuotientPerfectoid
public import SerrePositivity.BhattScholze.PerfectDeltaWittRecovery
public import SerrePositivity.BhattScholze.PerfectOrientedPrism
public import SerrePositivity.BhattScholze.PerfectoidRingEquiv

/-! # 一般の完全oriented prismの商のperfectoid性

著者公開版Theorem 3.10の商の向き。商のpねじれを許し、F7を要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.OrientedPrism
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 任意の完全oriented prismの標準商は整perfectoid。零環も含む。 -/
theorem quotient_isIntegralPerfectoid (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) : IsIntegralPerfectoid (A ⧸ P.ideal) p := by
  rcases subsingleton_or_nontrivial A with hs | hn
  · let := hs
    exact Or.inl inferInstance
  · let := hn
    let := P.isAdicComplete_p_of_perfect hP
    let := P.isAdicComplete_generator
    have hp : ¬ IsUnit (p : A) := by
      intro hu
      let : Subsingleton A := subsingleton_of_isUnit_natCast_of_isHausdorff p A hu
      exact zero_ne_one (Subsingleton.elim (0 : A) 1)
    let : Fact (¬ IsUnit (p : A)) := ⟨hp⟩
    let := hP.perfectRing_mod_p
    let k := ModP A p
    let e := perfectDeltaWittRecoveryEquiv P.deltaStructure hP
    let d := e.symm P.generator
    have hd : (wittDeltaStructure p k).IsDistinguished d :=
      (perfectDeltaWittRecoveryEquiv_symm_isDeltaHom P.deltaStructure hP).map_isDistinguished
        (P.isDistinguished_of_perfect hP)
    let : IsAdicComplete (Ideal.span {d}) (WittVector p k) := by
      have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {P.generator}) e.symm).mpr
        P.isAdicComplete_generator
      simpa only [Ideal.map_span, Set.image_singleton] using h
    let eq : WittVector p k ⧸ Ideal.span {d} ≃+* A ⧸ P.ideal :=
      Ideal.quotientEquiv _ _ e (by
        simp only [ideal, Ideal.map_span, Set.image_singleton, d,
          RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply])
    exact isIntegralPerfectoid_of_ringEquiv p eq
      (wittCompleteDistinguishedQuotient_isIntegralPerfectoid p k d hd)

end SerrePositivity.BhattScholze.OrientedPrism
