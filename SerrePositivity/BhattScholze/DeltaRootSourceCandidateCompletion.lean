module

public import SerrePositivity.BhattScholze.DeltaRootSourceRawCoefficients
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReflection

/-! # 既存候補への標準射の実p,d逐次完備化からの一意延長 -/

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
local notation "B" => DeltaRootPrismCarrier D d b
local notation "Pre" => DeltaRootPCompletion D d b
local notation "dd" => deltaRootPCompletionGenerator D d b
local notation "X" => DeltaRootSourceCoefficientObject d D b
local notation "Y" => DeltaRootPrismCoefficientObject D d b
local notation "Cp" => boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => boundedAboveDerivedCompletionFunctor A d
local notation "Up" => boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => boundedAboveDerivedCompletionUnit A d

/-- 既存候補の次数零対象は、元のA上でp導来完備。 -/
theorem deltaRootPrismCoefficientObject_isComplete_p : IsComplete A (p : A) (Y).obj := by
  let := deltaRootPrismCommRing D d b
  let := deltaRootPrismCoefficientAlgebra D d b
  let : Module A B := Algebra.toModule
  change IsModuleComplete A (p : A) (ModuleCat.of A B)
  apply (isModuleComplete_algebraMap_iff A B (p : A) B).mp
  simpa only [map_natCast] using pdCompletionH0_self_complete_p Pre p dd

/-- 同じ既存候補は、元のAのdについて導来完備。 -/
theorem deltaRootPrismCoefficientObject_isComplete_d : IsComplete A d (Y).obj := by
  let := deltaRootPrismCommRing D d b
  let := deltaRootPrismCoefficientAlgebra D d b
  let : Module A B := Algebra.toModule
  change IsModuleComplete A d (ModuleCat.of A B)
  apply (isModuleComplete_algebraMap_iff A B d B).mp
  have he : algebraMap A B d = pdCompletionUnit Pre p dd dd := rfl
  rw [he]
  exact pdCompletionH0_self_complete_d Pre p dd

/-- 元の標準射を、実p完備化後の源から一意な延長として構成する。 -/
def deltaRootSourceCandidatePCompletionMap : (Cp).obj X ⟶ Y :=
  ObjectProperty.homMk
    ((derivedComplexCompletionHomEquiv A (p : A) (X).obj (Y).obj
      (deltaRootPrismCoefficientObject_isComplete_p D d b)).symm
        (deltaRootSourceCandidateMap D d b).hom)

/-- p完備化後の標準射は元のp完備化単位を保つ。 -/
theorem deltaRootSourceCandidatePCompletionMap_unit :
    (Up).app X ≫ deltaRootSourceCandidatePCompletionMap D d b =
      deltaRootSourceCandidateMap D d b := by
  apply InducedCategory.hom_ext
  exact (derivedComplexCompletionHomEquiv A (p : A) (X).obj (Y).obj
    (deltaRootPrismCoefficientObject_isComplete_p D d b)).apply_symm_apply
      (deltaRootSourceCandidateMap D d b).hom

/-- 元の実p,d逐次完備化源から、既存候補への標準延長射。 -/
def deltaRootSourceCandidateIteratedMap :
    DeltaRootSourceIteratedPDCompletion D d b ⟶ Y :=
  ObjectProperty.homMk
    ((derivedComplexCompletionHomEquiv A d ((Cp).obj X).obj (Y).obj
      (deltaRootPrismCoefficientObject_isComplete_d D d b)).symm
        (deltaRootSourceCandidatePCompletionMap D d b).hom)

/-- 逐次完備化後の射は最後のd完備化単位を保つ。 -/
theorem deltaRootSourceCandidateIteratedMap_d_unit :
    (Ud).app ((Cp).obj X) ≫ deltaRootSourceCandidateIteratedMap D d b =
      deltaRootSourceCandidatePCompletionMap D d b := by
  apply InducedCategory.hom_ext
  exact (derivedComplexCompletionHomEquiv A d ((Cp).obj X).obj (Y).obj
    (deltaRootPrismCoefficientObject_isComplete_d D d b)).apply_symm_apply
      (deltaRootSourceCandidatePCompletionMap D d b).hom

/-- 標準延長は、元の実p,d合成完備化単位と可換。 -/
theorem deltaRootSourceCandidateIteratedMap_unit :
    ((Up).app X ≫ (Ud).app ((Cp).obj X)) ≫ deltaRootSourceCandidateIteratedMap D d b =
      deltaRootSourceCandidateMap D d b := by
  rw [Category.assoc, deltaRootSourceCandidateIteratedMap_d_unit,
    deltaRootSourceCandidatePCompletionMap_unit]

/-- 合成標準単位上で元の射に一致する延長は、この標準延長だけである。 -/
theorem deltaRootSourceCandidateIteratedMap_unique
    (g : DeltaRootSourceIteratedPDCompletion D d b ⟶ Y)
    (hg : ((Up).app X ≫ (Ud).app ((Cp).obj X)) ≫ g = deltaRootSourceCandidateMap D d b) :
    g = deltaRootSourceCandidateIteratedMap D d b := by
  have h : (Up).app X ≫ ((Ud).app ((Cp).obj X) ≫ g) =
      (Up).app X ≫ ((Ud).app ((Cp).obj X) ≫ deltaRootSourceCandidateIteratedMap D d b) := by
    simpa only [Category.assoc] using hg.trans (deltaRootSourceCandidateIteratedMap_unit D d b).symm
  apply InducedCategory.hom_ext
  apply derivedComplexCompletionHom_ext A d (deltaRootPrismCoefficientObject_isComplete_d D d b)
  apply derivedComplexCompletionHom_ext A (p : A)
    (deltaRootPrismCoefficientObject_isComplete_p D d b)
  exact congrArg (fun f => f.hom) h

/-- 同じ具体的源・候補・標準射についての一意延長の存在。 -/
theorem existsUnique_deltaRootSourceCandidateIteratedMap :
    ∃! g : DeltaRootSourceIteratedPDCompletion D d b ⟶ Y,
      ((Up).app X ≫ (Ud).app ((Cp).obj X)) ≫ g = deltaRootSourceCandidateMap D d b := by
  exact ⟨deltaRootSourceCandidateIteratedMap D d b,
    deltaRootSourceCandidateIteratedMap_unit D d b,
    fun g hg => deltaRootSourceCandidateIteratedMap_unique D d b g hg⟩

end SerrePositivity.BhattScholze
