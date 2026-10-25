module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootSourceRawH0Delta
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.DeltaRootPrismBaseMap

/-! # 実源H0から既存prism候補への標準δ射 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "α" => deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d)
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "C₀" => algebraMap A L
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "j" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedTensor
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "AlgX" => boundedAboveDerivedTensorAlgebra (R := L) P L
local notation "HX" => ModuleCat.carrier
  (CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat L) 0)
    (Functor.obj DerivedCategory.Minus.ι (CommMon.X AlgX)))

/-- 元の実H0から既存prism候補へ、標準raw比較と既存候補射を合成した環射。 -/
def deltaRootSourceH0CandidateMap :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    letI := deltaRootPrismCommRing D d b
    HX →+* DeltaRootPrismCarrier D d b := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  let := deltaRootPrismCommRing D d b
  exact (deltaRootPrismRawMap D d b).comp
    (deltaRootSourceRawH0AlgEquiv D d b).toRingHom

/-- distinguished生成元の場合、同じ標準候補射は実H0のδ構造と両立する。 -/
theorem deltaRootSourceH0CandidateMap_isDeltaHom (hd : D.IsDistinguished d) :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    letI := deltaRootPrismCommRing D d b
    (deltaRootSourceRawH0DeltaStructure D d b).IsDeltaHom
      (deltaRootPrism D d b hd).deltaStructure (deltaRootSourceH0CandidateMap D d b) := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  let := deltaRootPrismCommRing D d b
  exact (deltaRootPrismRawMap_isDeltaHom D d b hd).comp
    (deltaRootSourceRawH0AlgEquiv_isDeltaHom D d b).1

/-- 元Aの標準係数射は、既存候補の係数射そのものへ送られる。 -/
theorem deltaRootSourceH0CandidateMap_comp_coefficient :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    letI := deltaRootPrismCommRing D d b
    (deltaRootSourceH0CandidateMap D d b).comp ((algebraMap L HX).comp C₀) =
      deltaRootPrismCoefficientMap D d b := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  let := deltaRootPrismCommRing D d b
  apply RingHom.ext
  intro a
  change deltaRootPrismRawMap D d b
      (deltaRootSourceRawH0AlgEquiv D d b (algebraMap L HX (C₀ a))) = _
  rw [deltaRootSourceRawH0AlgEquiv_algebraMap]
  change deltaRootPrismRawMap D d b (j (β (MvPolynomial.C (MvPolynomial.C a)))) = _
  rw [deltaDivisionSourceEval_C]
  rfl

/-- 同じ候補環射の関数は、元の実augmentationのH0写像を用いた標準関数と一致。 -/
theorem deltaRootSourceH0CandidateMap_augmentation :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    letI := deltaRootPrismCommRing D d b
    ∀ h : HX, deltaRootSourceH0CandidateMap D d b h =
      deltaRootPrismRawMap D d b
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat L) 0).hom.app
          (DeltaRootSourceRawModule D d b)
          ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
            (deltaRootSourceRawAugmentation D d b).hom h)) := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  let := deltaRootPrismCommRing D d b
  intro h
  change deltaRootPrismRawMap D d b (deltaRootSourceRawH0AlgEquiv D d b h) = _
  rw [deltaRootSourceRawH0AlgEquiv_augmentation]

end SerrePositivity.BhattScholze
