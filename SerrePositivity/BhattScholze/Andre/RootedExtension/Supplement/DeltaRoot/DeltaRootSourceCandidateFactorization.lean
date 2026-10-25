module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootSourceCandidateCompletion

/-! # 候補比較射のraw逐次完備化を通る因子分解 -/

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
local notation "Z" => DeltaRootSourceRawCoefficientObject D d b
local notation "Y" => DeltaRootPrismCoefficientObject D d b
local notation "Cp" => boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => boundedAboveDerivedCompletionFunctor A d
local notation "Up" => boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => boundedAboveDerivedCompletionUnit A d

/-- raw係数対象から、同じ標準A作用を持つ既存候補への射。 -/
def deltaRootRawCandidateMap : Z ⟶ Y := by
  letI := deltaRootPrismCommRing D d b
  letI := deltaRootPrismCoefficientAlgebra D d b
  letI : Module A (DeltaRootPrismCarrier D d b) := Algebra.toModule
  exact (deltaRootSourceRawCoefficientSingleIso D d b).hom ≫
    boundedAboveDerivedSingleFunctor.map
      (ModuleCat.ofHom (deltaRootSourceRawCandidateLinearMap D d b))

/-- 元の標準射のraw次数零対象を通る因子分解。 -/
theorem deltaRootSourceCandidateMap_raw_factorization :
    deltaRootSourceRawCoefficientAugmentation D d b ≫ deltaRootRawCandidateMap D d b =
      deltaRootSourceCandidateMap D d b := rfl

/-- raw側の実p完備化からの延長。 -/
def deltaRootRawCandidatePCompletionMap : (Cp).obj Z ⟶ Y :=
  ObjectProperty.homMk
    ((derivedComplexCompletionHomEquiv A (p : A) (Z).obj (Y).obj
      (deltaRootPrismCoefficientObject_isComplete_p D d b)).symm
        (deltaRootRawCandidateMap D d b).hom)

/-- raw側のp完備化単位との可換性。 -/
theorem deltaRootRawCandidatePCompletionMap_unit :
    (Up).app Z ≫ deltaRootRawCandidatePCompletionMap D d b =
      deltaRootRawCandidateMap D d b := by
  apply InducedCategory.hom_ext
  exact (derivedComplexCompletionHomEquiv A (p : A) (Z).obj (Y).obj
    (deltaRootPrismCoefficientObject_isComplete_p D d b)).apply_symm_apply
      (deltaRootRawCandidateMap D d b).hom

/-- raw側の実p,d逐次完備化からの延長。 -/
def deltaRootRawCandidateIteratedMap : DeltaRootSourceRawIteratedCompletion D d b ⟶ Y :=
  ObjectProperty.homMk
    ((derivedComplexCompletionHomEquiv A d ((Cp).obj Z).obj (Y).obj
      (deltaRootPrismCoefficientObject_isComplete_d D d b)).symm
        (deltaRootRawCandidatePCompletionMap D d b).hom)

/-- raw側のd完備化単位との可換性。 -/
theorem deltaRootRawCandidateIteratedMap_d_unit :
    (Ud).app ((Cp).obj Z) ≫ deltaRootRawCandidateIteratedMap D d b =
      deltaRootRawCandidatePCompletionMap D d b := by
  apply InducedCategory.hom_ext
  exact (derivedComplexCompletionHomEquiv A d ((Cp).obj Z).obj (Y).obj
    (deltaRootPrismCoefficientObject_isComplete_d D d b)).apply_symm_apply
      (deltaRootRawCandidatePCompletionMap D d b).hom

/-- raw側の合成標準単位との可換性。 -/
theorem deltaRootRawCandidateIteratedMap_unit :
    ((Up).app Z ≫ (Ud).app ((Cp).obj Z)) ≫ deltaRootRawCandidateIteratedMap D d b =
      deltaRootRawCandidateMap D d b := by
  rw [Category.assoc, deltaRootRawCandidateIteratedMap_d_unit,
    deltaRootRawCandidatePCompletionMap_unit]

/-- 実逐次完備化から候補への直接延長は、raw側を通る延長と一致する。 -/
theorem deltaRootSourceCandidateIteratedMap_raw_factorization :
    deltaRootSourceRawIteratedComparison D d b ≫ deltaRootRawCandidateIteratedMap D d b =
      deltaRootSourceCandidateIteratedMap D d b := by
  apply deltaRootSourceCandidateIteratedMap_unique
  rw [← Category.assoc, deltaRootSourceRawIteratedComparison_unit, Category.assoc,
    deltaRootRawCandidateIteratedMap_unit, deltaRootSourceCandidateMap_raw_factorization]

end SerrePositivity.BhattScholze
