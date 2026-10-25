module

public import SerrePositivity.BhattScholze.Prism.FontaineKernelNaturality

/-! # B4-5：源のFontaine生成元を共用するWitt商表示

非零枝のFontaine写像のデータを入力し、標準写像と両立する具体的商同型を構成する。
源の生成元の像を使うため、余積の両因子の表示に同じ基底生成元を利用できる。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R S : Type u} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
variable [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))]
variable [IsAdicComplete (Ideal.span {(p : R)}) R]
variable [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- 源のdistinguished核元の像を使う、終域の標準Witt商表示。 -/
def fontaineBaseWittQuotientEquiv
    (f : R →+* S) (d : WittVector p (PreTilt R p))
    (hd : (wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hzero : WittVector.fontaineTheta R p d = 0)
    (hF : Function.Surjective (fun x : ModP S p ↦ x ^ p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal) :
    WittVector p (PreTilt S p) ⧸
      Ideal.span {WittVector.map (Perfection.map p (modPMap p f)) d} ≃+* S :=
  (Ideal.quotEquivOfEq (fontaineKernel_eq_span_image_distinguished p f d hd hzero hker).symm).trans
    (RingHom.quotientKerEquivOfSurjective (fun x ↦ surjective_fontaineTheta hF x))

/-- 商表示の順射と標準商射の合成は、標準Fontaine写像。 -/
theorem fontaineBaseWittQuotientEquiv_comp_mk
    (f : R →+* S) (d : WittVector p (PreTilt R p))
    (hd : (wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hzero : WittVector.fontaineTheta R p d = 0)
    (hF : Function.Surjective (fun x : ModP S p ↦ x ^ p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal) :
    (fontaineBaseWittQuotientEquiv p f d hd hzero hF hker).toRingHom.comp
      (Ideal.Quotient.mk _) = WittVector.fontaineTheta S p := by
  apply RingHom.ext
  intro x
  rfl

/-- 商表示の逆射は、標準Fontaine写像を標準商射へ移す。 -/
theorem fontaineBaseWittQuotientEquiv_symm_comp_fontaineTheta
    (f : R →+* S) (d : WittVector p (PreTilt R p))
    (hd : (wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hzero : WittVector.fontaineTheta R p d = 0)
    (hF : Function.Surjective (fun x : ModP S p ↦ x ^ p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal) :
    (fontaineBaseWittQuotientEquiv p f d hd hzero hF hker).symm.toRingHom.comp
      (WittVector.fontaineTheta S p) = Ideal.Quotient.mk _ := by
  let e := fontaineBaseWittQuotientEquiv p f d hd hzero hF hker
  apply RingHom.ext
  intro x
  have he : e (Ideal.Quotient.mk _ x) = WittVector.fontaineTheta S p x :=
    RingHom.congr_fun (fontaineBaseWittQuotientEquiv_comp_mk p f d hd hzero hF hker) x
  change e.symm (WittVector.fontaineTheta S p x) = Ideal.Quotient.mk _ x
  rw [← he, e.symm_apply_apply]

end SerrePositivity.BhattScholze
