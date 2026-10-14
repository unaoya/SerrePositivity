module

public import SerrePositivity.BhattScholze.FontaineNaturality
public import SerrePositivity.BhattScholze.WittDistinguished
public import SerrePositivity.CommutativeAlgebra.PerfectoidFrobeniusCriterion

/-! # B4-5：Fontaine核のdistinguished生成元の底変換

既存の核判定と自然性を使い、源の生成元の像が終域の核を生成することを示す。
環そのもののp正則性を要求しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R S : Type u} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
variable [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))]
variable [IsAdicComplete (Ideal.span {(p : R)}) R]
variable [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- Fontaine核内のdistinguished元の標準Witt像は、単項な終域のFontaine核を生成する。 -/
theorem fontaineKernel_eq_span_image_distinguished
    (f : R →+* S) (d : WittVector p (PreTilt R p))
    (hd : (wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hzero : WittVector.fontaineTheta R p d = 0)
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal) :
    RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {WittVector.map (Perfection.map p (modPMap p f)) d} := by
  let m : WittVector p (PreTilt R p) →+* WittVector p (PreTilt S p) :=
    WittVector.map (Perfection.map p (modPMap p f))
  have hdist := (wittDeltaStructure_map_isDeltaHom p (PreTilt R p)
    (Perfection.map p (modPMap p f))).map_isDistinguished hd
  have hunit : IsUnit ((m d).coeff 1) :=
    (wittDeltaStructure_isDistinguished_iff p (PreTilt S p) (m d)).mp hdist
  apply PerfectoidFrobeniusCriterion.ker_fontaineTheta_eq_span_of_firstCoeff_unit
    S p hker (m d)
  · have he := RingHom.congr_fun (fontaineTheta_natural p f) d
    change WittVector.fontaineTheta S p (m d) = f (WittVector.fontaineTheta R p d) at he
    rw [hzero, map_zero] at he
    exact he
  · exact hunit.map (PreTilt.coeff 0)

end SerrePositivity.BhattScholze
