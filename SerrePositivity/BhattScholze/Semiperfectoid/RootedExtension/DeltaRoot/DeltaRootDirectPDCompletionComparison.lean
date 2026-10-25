module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaPerfectionPDCompletionComparison
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootPrismBaseMap

/-! # 既存根添加候補と直接PD完備化の標準環・商比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "ι" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "z" => ι (MvPolynomial.C d)
local notation "C" => DeltaPerfection F
local notation "x" => deltaPerfectionOf F 0 z
local notation "H" => PDCompletionH0 C p x
local notation "s" => pdCompletionUnit C p x
local notation "r₀" => RingHom.comp s (deltaPerfectionOf F 0)

/-- 根raw環のδ完全化の直接PD完備化は、既存prism台環候補と標準環同型。 -/
def deltaRootDirectPDCompletionEquiv :
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    H ≃+* DeltaRootPrismCarrier D d b := by
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  exact deltaPerfectionPDCompletionEquiv F z

/-- 環比較は、元の根raw環からの両標準射を保つ。 -/
theorem deltaRootDirectPDCompletionEquiv_comp_raw :
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    (deltaRootDirectPDCompletionEquiv D d b).toRingHom.comp r₀ =
      deltaRootPrismRawMap D d b := by
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  exact (deltaPerfectionPDCompletionEquiv_spec F z).2.2

/-- 環比較は、元Aの具体的標準係数射を保つ。 -/
theorem deltaRootDirectPDCompletionEquiv_comp_coefficient :
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    (deltaRootDirectPDCompletionEquiv D d b).toRingHom.comp
        ((r₀).comp ((ι).comp MvPolynomial.C)) = deltaRootPrismCoefficientMap D d b := by
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  rw [← RingHom.comp_assoc, deltaRootDirectPDCompletionEquiv_comp_raw]
  rfl

/-- 直接PD完備化の選択元像は、既存候補の同じ選択元像へ移る。 -/
theorem deltaRootDirectPDCompletionEquiv_generator :
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    deltaRootDirectPDCompletionEquiv D d b (s x) =
      pdCompletionUnit (DeltaRootPCompletion D d b) p
        (deltaRootPCompletionGenerator D d b) (deltaRootPCompletionGenerator D d b) := by
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  exact RingHom.congr_fun (deltaRootDirectPDCompletionEquiv_comp_raw D d b) z

/-- 生成元の標準主イデアル商は、既存の実perfectoid候補と環同型。 -/
def deltaRootDirectPDCompletionQuotientEquiv (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    (H ⧸ Ideal.span {s x}) ≃+* DeltaRootPerfectoidCandidate D d b hd := by
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  exact Ideal.quotientEquiv _ _ (deltaRootDirectPDCompletionEquiv D d b) (by
    rw [Ideal.map_span, Set.image_singleton]
    symm
    change Ideal.span (Set.singleton (deltaRootDirectPDCompletionEquiv D d b (s x))) =
      Ideal.span (Set.singleton (pdCompletionUnit (DeltaRootPCompletion D d b) p
        (deltaRootPCompletionGenerator D d b) (deltaRootPCompletionGenerator D d b)))
    rw [deltaRootDirectPDCompletionEquiv_generator])

/-- 商比較は、代表元に具体的な標準環同型を適用する。 -/
theorem deltaRootDirectPDCompletionQuotientEquiv_mk (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    ∀ h : H, deltaRootDirectPDCompletionQuotientEquiv D d b hd (Ideal.Quotient.mk _ h) =
      Ideal.Quotient.mk _ (deltaRootDirectPDCompletionEquiv D d b h) := by
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  intro h
  rfl

/-- 商環比較は、元Aから既存perfectoid候補への同じ具体的係数射を保つ。 -/
theorem deltaRootDirectPDCompletionQuotientEquiv_comp_coefficient (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    (deltaRootDirectPDCompletionQuotientEquiv D d b hd).toRingHom.comp
        ((Ideal.Quotient.mk (Ideal.span {s x})).comp
          ((r₀).comp ((ι).comp MvPolynomial.C))) =
      deltaRootPerfectoidCandidateCoefficientMap D d b hd := by
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk (deltaRootPrism D d b hd).ideal
    (deltaRootDirectPDCompletionEquiv D d b
      (((r₀).comp ((ι).comp MvPolynomial.C)) a)) =
    Ideal.Quotient.mk (deltaRootPrism D d b hd).ideal (deltaRootPrismCoefficientMap D d b a)
  exact congrArg (Ideal.Quotient.mk (deltaRootPrism D d b hd).ideal)
    (RingHom.congr_fun (deltaRootDirectPDCompletionEquiv_comp_coefficient D d b) a)

/-- 直接PD完備化の同じ具体的生成元商も、既存候補から整perfectoid性を受け取る。 -/
theorem deltaRootDirectPDCompletionQuotient_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing C p x
    IsIntegralPerfectoid (H ⧸ Ideal.span {s x}) p := by
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  exact isIntegralPerfectoid_of_ringEquiv p
    (deltaRootDirectPDCompletionQuotientEquiv D d b hd).symm
    (deltaRootPerfectoidCandidate_isIntegralPerfectoid D d b hd)

end SerrePositivity.BhattScholze
