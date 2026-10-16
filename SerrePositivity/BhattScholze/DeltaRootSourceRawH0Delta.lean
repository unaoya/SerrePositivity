module

public import SerrePositivity.BhattScholze.DeltaRootSourceRawH0Algebra
public import SerrePositivity.BhattScholze.DeltaDivisionSourceTensorDelta
public import SerrePositivity.BhattScholze.DeltaTransport

/-! # 同じ実二因子源H0のδ構造と標準係数射 -/

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

/-- 同じ実H0の共通環構造上に、標準raw同型と既存W2写像でδ構造を移す。 -/
def deltaRootSourceRawH0DeltaStructure :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    DeltaStructure p HX := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  let e := deltaRootSourceRawH0AlgEquiv D d b
  exact (F).comapEquiv e.toRingEquiv

/-- H0上のδは、標準raw代数同型を通じた元のδの共役そのもの。 -/
theorem deltaRootSourceRawH0Delta_apply :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    ∀ h : HX, (deltaRootSourceRawH0DeltaStructure D d b).delta h =
      (deltaRootSourceRawH0AlgEquiv D d b).symm
        ((F).delta (deltaRootSourceRawH0AlgEquiv D d b h)) := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  intro h
  exact (F).comapEquiv_delta (deltaRootSourceRawH0AlgEquiv D d b).toRingEquiv h

/-- 同じ標準H0/raw代数同型の両方向は、具体的δ構造と両立する。 -/
theorem deltaRootSourceRawH0AlgEquiv_isDeltaHom :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    (deltaRootSourceRawH0DeltaStructure D d b).IsDeltaHom F
        (deltaRootSourceRawH0AlgEquiv D d b).toRingHom ∧
      (F).IsDeltaHom (deltaRootSourceRawH0DeltaStructure D d b)
        (deltaRootSourceRawH0AlgEquiv D d b).symm.toRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  let e := (deltaRootSourceRawH0AlgEquiv D d b).toRingEquiv
  exact ⟨(F).comapEquiv_isDeltaHom e, (F).comapEquiv_symm_isDeltaHom e⟩

/-- rawから同型の逆で得る元A係数射は、元のL作用を制限した標準係数射と同じ。 -/
theorem deltaRootSourceRawH0Coefficient_eq :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    (deltaRootSourceRawH0AlgEquiv D d b).symm.toRingHom.comp ((j).comp MvPolynomial.C) =
      (algebraMap L HX).comp C₀ := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  apply RingHom.ext
  intro a
  apply (deltaRootSourceRawH0AlgEquiv D d b).injective
  change deltaRootSourceRawH0AlgEquiv D d b
      ((deltaRootSourceRawH0AlgEquiv D d b).symm (j (MvPolynomial.C a))) =
    deltaRootSourceRawH0AlgEquiv D d b (algebraMap L HX (C₀ a))
  rw [(deltaRootSourceRawH0AlgEquiv D d b).apply_symm_apply,
    deltaRootSourceRawH0AlgEquiv_algebraMap]
  change j (MvPolynomial.C a) = j (β (MvPolynomial.C (MvPolynomial.C a)))
  rw [deltaDivisionSourceEval_C]

/-- 元Aの同じ標準係数射は、同じ実H0のδ構造へのδ射である。 -/
theorem deltaRootSourceRawH0Coefficient_isDeltaHom :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    D.IsDeltaHom (deltaRootSourceRawH0DeltaStructure D d b)
      ((algebraMap L HX).comp C₀) := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  rw [← deltaRootSourceRawH0Coefficient_eq]
  exact (deltaRootSourceRawH0AlgEquiv_isDeltaHom D d b).2.comp
    ((deltaAdjoinDivisionMap_isDeltaHom E (MvPolynomial.C d) r).comp
      (polynomialRankOneDeltaStructure_C_isDeltaHom σ D))

end SerrePositivity.BhattScholze
