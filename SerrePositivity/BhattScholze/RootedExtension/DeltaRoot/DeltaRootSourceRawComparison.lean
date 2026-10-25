module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSourceIteratedCompletionResidue
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionSourceTensor
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra

/-! # 元の実導来源からraw r/d包とその実完備化への比較射 -/

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
local notation "X" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

/-- raw包に、評価βを経由する元の実源L作用を明示した加群対象。 -/
def DeltaRootSourceRawModule : ModuleCat.{u} L := by
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  exact ModuleCat.of L Raw

/-- 通常二因子テンソルとraw包は、元の実源L上で線形同型。 -/
def deltaRootSourceOrdinaryTensorRawIso :
    (tensorLeft Mβ).obj Mα ≅ DeltaRootSourceRawModule D d b := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let e : P ⊗[L] L ≃ₐ[L] Raw :=
    AlgEquiv.ofRingEquiv (f := deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r) (by
      intro x
      change deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r
        (β x ⊗ₜ[L] 1) = (deltaAdjoinDivisionMap E (MvPolynomial.C d) r) (β x)
      rw [deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one])
  exact e.toLinearEquiv.toModuleIso

set_option maxHeartbeats 800000 in
-- Match the actual two scalar modules with the original bounded derived tensor object.
/-- 元の実導来二因子源から、raw次数零対象への標準augmentation。 -/
def deltaRootSourceRawAugmentation :
    X ⟶ boundedAboveDerivedSingleFunctor.obj (DeltaRootSourceRawModule D d b) := by
  let f : X ⟶ boundedAboveDerivedSingleFunctor.obj ((tensorLeft Mβ).obj Mα) :=
    ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation (R := L) Mβ).app Mα)
  exact f ≫ boundedAboveDerivedSingleFunctor.map (deltaRootSourceOrdinaryTensorRawIso D d b).hom

set_option maxHeartbeats 800000 in
-- Match the actual two scalar modules with the original bounded derived tensor object.
/-- 元の実導来二因子源のH0と実源作用付きraw包の比較。 -/
def deltaRootSourceRawH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat L) 0).obj (X).obj ≅
      DeltaRootSourceRawModule D d b :=
  (boundedAboveDerivedTensorModuleH0NatIso (R := L) Mβ).app Mα ≪≫
    deltaRootSourceOrdinaryTensorRawIso D d b

/-- raw標準augmentationはH0では同型である。高次の消滅はここでは主張しない。 -/
theorem deltaRootSourceRawAugmentation_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
      (deltaRootSourceRawAugmentation D d b).hom) := by
  have := derivedTensorAugmentation_h0_isIso (R := L) Mβ Mα
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
    (((boundedAboveDerivedTensorModuleAugmentation (R := L) Mβ).app Mα) ≫
      (DerivedCategory.singleFunctor (ModuleCat L) 0).map
        (deltaRootSourceOrdinaryTensorRawIso D d b).hom))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 元のAへ係数制限したraw次数零対象。 -/
abbrev DeltaRootSourceRawCoefficientObject :=
  (boundedAboveDerivedRestrictScalars C₀).obj
    (boundedAboveDerivedSingleFunctor.obj (DeltaRootSourceRawModule D d b))

set_option maxHeartbeats 800000 in
-- Compare the original tensor object through coefficient restriction and actual homology.
/-- 元のAへ係数制限した実導来源のH0も、raw包の同じ係数制限と同型。 -/
def deltaRootSourceRawCoefficientH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (DeltaRootSourceCoefficientObject d D b).obj ≅
      (ModuleCat.restrictScalars C₀).obj (DeltaRootSourceRawModule D d b) :=
  (derivedRestrictScalarsHomologyIso C₀ 0).app (X).obj ≪≫
    (ModuleCat.restrictScalars C₀).mapIso (deltaRootSourceRawH0Iso D d b)

/-- 元のA上の実導来源からraw次数零対象への、同じ実係数制限による射。 -/
def deltaRootSourceRawCoefficientAugmentation :
    DeltaRootSourceCoefficientObject d D b ⟶ DeltaRootSourceRawCoefficientObject D d b :=
  (boundedAboveDerivedRestrictScalars C₀).map (deltaRootSourceRawAugmentation D d b)

local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d

/-- raw次数零対象へ元と同じp,d逐次実導来完備化を施した対象。 -/
abbrev DeltaRootSourceRawIteratedCompletion :=
  (Cd).obj ((Cp).obj (DeltaRootSourceRawCoefficientObject D d b))

/-- 元の実逐次完備化源から、rawの同じ実逐次完備化への標準比較射。 -/
def deltaRootSourceRawIteratedComparison :
    DeltaRootSourceIteratedPDCompletion D d b ⟶ DeltaRootSourceRawIteratedCompletion D d b :=
  (Cd).map ((Cp).map (deltaRootSourceRawCoefficientAugmentation D d b))

/-- 完備化後の比較射は、元のp,d合成標準単位と可換。 -/
theorem deltaRootSourceRawIteratedComparison_unit :
    ((Up).app (DeltaRootSourceCoefficientObject d D b) ≫
      (Ud).app ((Cp).obj (DeltaRootSourceCoefficientObject d D b))) ≫
        deltaRootSourceRawIteratedComparison D d b =
      deltaRootSourceRawCoefficientAugmentation D d b ≫
        ((Up).app (DeltaRootSourceRawCoefficientObject D d b) ≫
          (Ud).app ((Cp).obj (DeltaRootSourceRawCoefficientObject D d b))) := by
  let f := deltaRootSourceRawCoefficientAugmentation D d b
  have hp := (Up).naturality f
  have hd := (Ud).naturality ((Cp).map f)
  simp only [CategoryTheory.Functor.id_map] at hp hd
  dsimp only [deltaRootSourceRawIteratedComparison]
  rw [Category.assoc, ← hd, ← Category.assoc, ← hp, Category.assoc]

end SerrePositivity.BhattScholze
