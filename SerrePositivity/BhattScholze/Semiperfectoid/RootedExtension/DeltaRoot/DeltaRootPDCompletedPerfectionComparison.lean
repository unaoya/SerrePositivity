module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaPDCompletionPerfectionComparison
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootDirectPDCompletionComparison
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootPrismBaseMap

/-! # PD完備化済み根δ環のδ完全化と既存候補の標準比較 -/

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
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "S" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "C" => DeltaPerfection G
local notation "x" => deltaPerfectionOf G 0 (v z)
local notation "H" => PDCompletionH0 C p x
local notation "s" => pdCompletionUnit C p x
local notation "r₀" => RingHom.comp (RingHom.comp s (deltaPerfectionOf G 0)) v

/-- PD完備化済み根δ環のδ完全化の実PD完備化は、既存prism台環候補と標準環同型。 -/
def deltaRootPDCompletedPerfectionEquiv :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    H ≃+* DeltaRootPrismCarrier D d b := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  exact (deltaPDCompletionPerfectionEquiv F z).symm.trans
    (deltaRootDirectPDCompletionEquiv D d b)

/-- 環比較は、元の根raw環からの両標準射を保つ。 -/
theorem deltaRootPDCompletedPerfectionEquiv_comp_raw :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    (deltaRootPDCompletedPerfectionEquiv D d b).toRingHom.comp r₀ =
      deltaRootPrismRawMap D d b := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  apply RingHom.ext
  intro a
  have h : (deltaPDCompletionPerfectionEquiv F z).symm (r₀ a) =
      pdCompletionUnit (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
        (deltaPerfectionOf F 0 a) :=
    RingHom.congr_fun (deltaPDCompletionPerfectionInverse_spec F z).2 a
  change deltaRootDirectPDCompletionEquiv D d b
    ((deltaPDCompletionPerfectionEquiv F z).symm (r₀ a)) = deltaRootPrismRawMap D d b a
  rw [h]
  exact RingHom.congr_fun (deltaRootDirectPDCompletionEquiv_comp_raw D d b) a

/-- 環比較は、元Aの具体的標準係数射を保つ。 -/
theorem deltaRootPDCompletedPerfectionEquiv_comp_coefficient :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    (deltaRootPDCompletedPerfectionEquiv D d b).toRingHom.comp
        ((r₀).comp ((ι).comp MvPolynomial.C)) = deltaRootPrismCoefficientMap D d b := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  rw [← RingHom.comp_assoc, deltaRootPDCompletedPerfectionEquiv_comp_raw]
  rfl

/-- PD先行構成の選択元像は、既存候補の同じ選択元像へ移る。 -/
theorem deltaRootPDCompletedPerfectionEquiv_generator :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    deltaRootPDCompletedPerfectionEquiv D d b (s x) =
      pdCompletionUnit (DeltaRootPCompletion D d b) p
        (deltaRootPCompletionGenerator D d b) (deltaRootPCompletionGenerator D d b) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  exact RingHom.congr_fun (deltaRootPDCompletedPerfectionEquiv_comp_raw D d b) z

/-- 生成元の標準主イデアル商は、既存の実perfectoid候補と環同型。 -/
def deltaRootPDCompletedPerfectionQuotientEquiv (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    (H ⧸ Ideal.span {s x}) ≃+* DeltaRootPerfectoidCandidate D d b hd := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  exact Ideal.quotientEquiv _ _ (deltaRootPDCompletedPerfectionEquiv D d b) (by
    rw [Ideal.map_span, Set.image_singleton]
    symm
    change Ideal.span (Set.singleton (deltaRootPDCompletedPerfectionEquiv D d b (s x))) =
      Ideal.span (Set.singleton (pdCompletionUnit (DeltaRootPCompletion D d b) p
        (deltaRootPCompletionGenerator D d b) (deltaRootPCompletionGenerator D d b)))
    rw [deltaRootPDCompletedPerfectionEquiv_generator])

/-- 商比較は、代表元に具体的な標準環同型を適用する。 -/
theorem deltaRootPDCompletedPerfectionQuotientEquiv_mk (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    ∀ h : H, deltaRootPDCompletedPerfectionQuotientEquiv D d b hd (Ideal.Quotient.mk _ h) =
      Ideal.Quotient.mk _ (deltaRootPDCompletedPerfectionEquiv D d b h) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  intro h
  rfl

/-- 商環比較は、元Aから既存perfectoid候補への同じ具体的係数射を保つ。 -/
theorem deltaRootPDCompletedPerfectionQuotientEquiv_comp_coefficient (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := deltaRootPrismCommRing D d b
    (deltaRootPDCompletedPerfectionQuotientEquiv D d b hd).toRingHom.comp
        ((Ideal.Quotient.mk (Ideal.span {s x})).comp
          ((r₀).comp ((ι).comp MvPolynomial.C))) =
      deltaRootPerfectoidCandidateCoefficientMap D d b hd := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk (deltaRootPrism D d b hd).ideal
    (deltaRootPDCompletedPerfectionEquiv D d b
      (((r₀).comp ((ι).comp MvPolynomial.C)) a)) =
    Ideal.Quotient.mk (deltaRootPrism D d b hd).ideal (deltaRootPrismCoefficientMap D d b a)
  exact congrArg (Ideal.Quotient.mk (deltaRootPrism D d b hd).ideal)
    (RingHom.congr_fun (deltaRootPDCompletedPerfectionEquiv_comp_coefficient D d b) a)

/-- PD先行構成の同じ具体的生成元商も、既存候補から整perfectoid性を受け取る。 -/
theorem deltaRootPDCompletedPerfectionQuotient_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    IsIntegralPerfectoid (H ⧸ Ideal.span {s x}) p := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := deltaRootPrismCommRing D d b
  exact isIntegralPerfectoid_of_ringEquiv p
    (deltaRootPDCompletedPerfectionQuotientEquiv D d b hd).symm
    (deltaRootPerfectoidCandidate_isIntegralPerfectoid D d b hd)

end SerrePositivity.BhattScholze
