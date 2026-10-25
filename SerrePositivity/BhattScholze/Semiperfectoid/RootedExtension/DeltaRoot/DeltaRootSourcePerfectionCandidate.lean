module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionPDCompletionMap
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.Source.DeltaRootDirectPDCompletionComparison
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.Source.DeltaRootSourceRawCoefficients

/-! # 元の実根添加源と完全化候補への標準三角図式 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "j" => RingHom.comp (deltaAdjoinDivisionMap E (MvPolynomial.C d) r) MvPolynomial.C
local notation "C" => DeltaPerfection F
local notation "κ" => deltaAlgebraPerfectionCoefficient F j
local notation "H" => PDCompletionH0 C p (κ d)
local notation "s" => pdCompletionUnit C p (κ d)
local notation "t" => RingHom.comp s κ
local notation "T" => DeltaRootPrismCarrier D d b
local notation "X∞" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule κ)

/-- raw根環の標準A作用から、δ完全化の同じA作用への標準線形射。 -/
def deltaRootRawPerfectionLinearMap : ModuleCat.of A Raw ⟶ baseChangeScalarModule κ := by
  let f : Raw →ₗ[A] baseChangeScalarModule κ :=
    { toFun := deltaPerfectionOf F 0
      map_add' := (deltaPerfectionOf F 0).map_add
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply, Algebra.smul_def]
        change deltaPerfectionOf F 0 (j a * x) = κ a * deltaPerfectionOf F 0 x
        exact (deltaPerfectionOf F 0).map_mul _ _ }
  exact { hom' := f }

/-- 元の実二因子源からraw δ完全化の正確なA作用付きsingleへの標準射。 -/
def deltaRootSourcePerfectionMap : DeltaRootSourceCoefficientObject d D b ⟶ X∞ :=
  deltaRootSourceRawCoefficientAugmentation D d b ≫
    (deltaRootSourceRawCoefficientSingleIso D d b).hom ≫
      boundedAboveDerivedSingleFunctor.map (deltaRootRawPerfectionLinearMap D d b)

/-- 直接PD・既存根候補の標準環同型を、正確な元Aの係数作用で線形化する。 -/
def deltaRootDirectPDCandidateLinearMap :
    letI := pdCompletionCommRing C p (κ d)
    letI := deltaRootPrismCommRing D d b
    letI := deltaRootPrismCoefficientAlgebra D d b
    letI : Module A T := Algebra.toModule
    baseChangeScalarModule t ⟶ ModuleCat.of A T := by
  let := pdCompletionCommRing C p (κ d)
  let := pdCompletionCommRing C p
    (deltaPerfectionOf F 0 ((deltaAdjoinDivisionMap E (MvPolynomial.C d) r) (MvPolynomial.C d)))
  let := deltaRootPrismCommRing D d b
  let := deltaRootPrismCoefficientAlgebra D d b
  let : Module A T := Algebra.toModule
  let e := deltaRootDirectPDCompletionEquiv D d b
  let f : baseChangeScalarModule t →ₗ[A] T :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro a h
        change H at h
        rw [RingHom.id_apply]
        change e (t a * h) = deltaRootPrismCoefficientMap D d b a * e h
        rw [map_mul]
        exact congrArg (fun z => z * e h)
          (RingHom.congr_fun (deltaRootDirectPDCompletionEquiv_comp_coefficient D d b) a) }
  exact { hom' := f }

/-- 同じA線形環比較をsingle射へ移す。 -/
def deltaRootDirectPDCandidateSingleMap :
    letI := pdCompletionCommRing C p (κ d)
    boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule t) ⟶
      DeltaRootPrismCoefficientObject D d b := by
  let := pdCompletionCommRing C p (κ d)
  let := pdCompletionCommRing C p
    (deltaPerfectionOf F 0 ((deltaAdjoinDivisionMap E (MvPolynomial.C d) r) (MvPolynomial.C d)))
  let := deltaRootPrismCommRing D d b
  let := deltaRootPrismCoefficientAlgebra D d b
  let : Module A T := Algebra.toModule
  exact boundedAboveDerivedSingleFunctor.map (deltaRootDirectPDCandidateLinearMap D d b)

/-- δ完全化と直接PD比較を通る射は、元の実源から既存候補への標準射そのもの。 -/
theorem deltaRootSourcePerfectionCandidate_triangle :
    letI := pdCompletionCommRing C p (κ d)
    deltaRootSourcePerfectionMap D d b ≫
        deltaAlgebraPerfectionPDCompletionSingleMap F j d ≫
          deltaRootDirectPDCandidateSingleMap D d b = deltaRootSourceCandidateMap D d b := by
  let := pdCompletionCommRing C p (κ d)
  let := pdCompletionCommRing C p
    (deltaPerfectionOf F 0 ((deltaAdjoinDivisionMap E (MvPolynomial.C d) r) (MvPolynomial.C d)))
  let := deltaRootPrismCommRing D d b
  let := deltaRootPrismCoefficientAlgebra D d b
  let : Module A T := Algebra.toModule
  have hm : deltaRootRawPerfectionLinearMap D d b ≫
      deltaAlgebraPerfectionPDCompletionLinearMap F j d ≫
        deltaRootDirectPDCandidateLinearMap D d b =
      ModuleCat.ofHom (deltaRootSourceRawCandidateLinearMap D d b) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change deltaRootDirectPDCompletionEquiv D d b
      (s (deltaPerfectionOf F 0 x)) = deltaRootPrismRawMap D d b x
    exact RingHom.congr_fun (deltaRootDirectPDCompletionEquiv_comp_raw D d b) x
  dsimp only [deltaRootSourcePerfectionMap, deltaAlgebraPerfectionPDCompletionSingleMap,
    deltaRootDirectPDCandidateSingleMap, deltaRootSourceCandidateMap]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [hm]

end SerrePositivity.BhattScholze
