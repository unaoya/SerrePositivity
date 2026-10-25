module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSourceRawComparison
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra

/-! # 元の実二因子源H0とraw環の標準代数比較 -/

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
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "j" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedTensor
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "AlgX" => boundedAboveDerivedTensorAlgebra (R := L) P L
local notation "HX" => ModuleCat.carrier
  (CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat L) 0)
    (Functor.obj DerivedCategory.Minus.ι (CommMon.X AlgX)))

/-- 共通の実テンソル代数対象は、元の二つの作用を持つ実源そのもの。 -/
def deltaRootSourceTensorAlgebraObjectIso :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    (AlgX).X ≅ X := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  exact Iso.refl _

set_option maxHeartbeats 800000 in
-- Keep both original scalar actions explicit in the actual H0 algebra comparison.
/-- 元の実二因子源のH0は、共通の環構造に関してraw環とL代数同型。 -/
def deltaRootSourceRawH0AlgEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    HX ≃ₐ[L] Raw := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  let e : P ⊗[L] L ≃ₐ[L] Raw :=
    AlgEquiv.ofRingEquiv (f := deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r) (by
      intro l
      change deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r (β l ⊗ₜ[L] 1) = j (β l)
      rw [deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one])
  let e0 : HX ≃ₐ[L] P ⊗[L] L := derivedTensorH0AlgEquiv (R := L) P L
  exact e0.trans e

/-- この同型は、元の実源Lの標準係数作用をβ経由のraw作用へ送る。 -/
theorem deltaRootSourceRawH0AlgEquiv_algebraMap :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    ∀ l : L, deltaRootSourceRawH0AlgEquiv D d b (algebraMap L HX l) = j (β l) := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  intro l
  exact (deltaRootSourceRawH0AlgEquiv D d b).commutes l

set_option maxHeartbeats 800000 in
-- Match the original augmentation through the two native scalar modules and canonical single H0.
/-- 代数比較の関数は、元の標準augmentationのH0写像と標準single比較の合成そのもの。 -/
theorem deltaRootSourceRawH0AlgEquiv_augmentation :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L L := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
    letI : Module L Raw := Algebra.toModule
    letI : CommRing HX := derivedH0CommRing AlgX
    letI : Algebra L HX := derivedH0Algebra AlgX
    ∀ h : HX, deltaRootSourceRawH0AlgEquiv D d b h =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat L) 0).hom.app
        (DeltaRootSourceRawModule D d b)
        ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
          (deltaRootSourceRawAugmentation D d b).hom h) := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let : CommRing HX := derivedH0CommRing AlgX
  let : Algebra L HX := derivedH0Algebra AlgX
  intro h
  let H0 := DerivedCategory.homologyFunctor (ModuleCat L) 0
  let f := (boundedAboveDerivedTensorModuleAugmentation Mβ).app Mα
  let U := (deltaRootSourceOrdinaryTensorRawIso D d b).hom
  have hn := derivedSingleH0_map_apply U (H0.map f h)
  change deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r
    (derivedTensorH0AlgHom (R := L) P L h) = _
  rw [derivedTensorH0AlgHom_apply]
  change U.hom
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat L) 0).hom.app
      ((tensorLeft Mβ).obj Mα) (H0.map f h)) =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat L) 0).hom.app
      (DeltaRootSourceRawModule D d b)
      (H0.map (f ≫ (DerivedCategory.singleFunctor (ModuleCat L) 0).map U) h)
  rw [Functor.map_comp]
  exact hn.symm

end SerrePositivity.BhattScholze
