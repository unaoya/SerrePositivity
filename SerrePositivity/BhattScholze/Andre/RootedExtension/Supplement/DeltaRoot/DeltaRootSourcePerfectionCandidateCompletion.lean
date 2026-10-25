module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootSourcePerfectionCandidate
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootSourceCandidateCompletion

/-! # 元の実根添加源から既存候補への標準三角図式の逐次完備化 -/

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
local notation "X₀" => DeltaRootSourceCoefficientObject d D b
local notation "X∞" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule κ)
local notation "Cp" => boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => boundedAboveDerivedCompletionFunctor A d
local notation "Up" => boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => boundedAboveDerivedCompletionUnit A d

/-- 元の実源からδ完全化singleへの標準射を、同じ両実完備化へ適用する。 -/
def deltaRootSourcePerfectionIteratedMap :
    DeltaRootSourceIteratedPDCompletion D d b ⟶
      DeltaAlgebraPerfectionIteratedPDCompletion F j d :=
  (Cd).map ((Cp).map (deltaRootSourcePerfectionMap D d b))

/-- この実逐次射は、元の両合成標準単位と自然に可換。 -/
theorem deltaRootSourcePerfectionIteratedMap_unit :
    (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
        deltaRootSourcePerfectionIteratedMap D d b =
      deltaRootSourcePerfectionMap D d b ≫
        (((Up).app X∞) ≫ (Ud).app ((Cp).obj X∞)) := by
  let f := deltaRootSourcePerfectionMap D d b
  have hp := (Up).naturality f
  have hd := (Ud).naturality ((Cp).map f)
  simp only [Functor.id_map] at hp hd
  change ((Up).app X₀ ≫ (Ud).app ((Cp).obj X₀)) ≫ (Cd).map ((Cp).map f) = _
  calc
    _ = (Up).app X₀ ≫ ((Ud).app ((Cp).obj X₀) ≫ (Cd).map ((Cp).map f)) :=
      Category.assoc _ _ _
    _ = ((Up).app X₀ ≫ (Cp).map f) ≫ (Ud).app ((Cp).obj X∞) := by
      rw [← hd, ← Category.assoc]
    _ = _ := by rw [← hp, Category.assoc]

/-- δ完全化・直接PD標準射・既存候補比較を通る実逐次射は、既存の標準延長に一致する。 -/
theorem deltaRootSourcePerfectionCandidate_iterated_triangle :
    letI := pdCompletionCommRing C p (κ d)
    deltaRootSourcePerfectionIteratedMap D d b ≫
        deltaAlgebraPerfectionPDCompletionIteratedMap F j d ≫
          deltaRootDirectPDCandidateSingleMap D d b =
      deltaRootSourceCandidateIteratedMap D d b := by
  let := pdCompletionCommRing C p (κ d)
  apply deltaRootSourceCandidateIteratedMap_unique D d b
  calc
    _ = ((((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
        deltaRootSourcePerfectionIteratedMap D d b) ≫
          deltaAlgebraPerfectionPDCompletionIteratedMap F j d ≫
            deltaRootDirectPDCandidateSingleMap D d b := by simp only [Category.assoc]
    _ = (deltaRootSourcePerfectionMap D d b ≫
        (((Up).app X∞) ≫ (Ud).app ((Cp).obj X∞))) ≫
          deltaAlgebraPerfectionPDCompletionIteratedMap F j d ≫
            deltaRootDirectPDCandidateSingleMap D d b := by
      rw [deltaRootSourcePerfectionIteratedMap_unit]
    _ = deltaRootSourcePerfectionMap D d b ≫
        deltaAlgebraPerfectionPDCompletionSingleMap F j d ≫
          deltaRootDirectPDCandidateSingleMap D d b := by
      simpa only [Category.assoc] using congrArg
        (fun q => deltaRootSourcePerfectionMap D d b ≫ q ≫
          deltaRootDirectPDCandidateSingleMap D d b)
        (deltaAlgebraPerfectionPDCompletionIteratedMap_unit F j d)
    _ = _ := deltaRootSourcePerfectionCandidate_triangle D d b

end SerrePositivity.BhattScholze
