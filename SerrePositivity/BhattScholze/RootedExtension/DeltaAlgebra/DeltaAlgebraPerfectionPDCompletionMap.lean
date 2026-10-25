module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionCompletionRestriction
public import SerrePositivity.BhattScholze.Prism.PDCompletionInterface
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReflection

/-! # 実δ完全化逐次対象から直接PD完備化H0への標準一意延長 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "C" => DeltaPerfection E
local notation "κ" => deltaAlgebraPerfectionCoefficient E j
local notation "H" => PDCompletionH0 C p (κ d)
local notation "s" => pdCompletionUnit C p (κ d)
local notation "t" => RingHom.comp s κ
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule κ)
local notation "Y" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule t)
local notation "Cp" => boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => boundedAboveDerivedCompletionFunctor A d
local notation "Up" => boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => boundedAboveDerivedCompletionUnit A d

/-- 直接PD完備化の元の標準環射は、元Aの正確な作用について線形。 -/
def deltaAlgebraPerfectionPDCompletionLinearMap :
    letI := pdCompletionCommRing C p (κ d)
    baseChangeScalarModule κ ⟶ baseChangeScalarModule t := by
  let := pdCompletionCommRing C p (κ d)
  let f : baseChangeScalarModule κ →ₗ[A] baseChangeScalarModule t :=
    { toFun := fun c => s c
      map_add' := (s).map_add
      map_smul' := by
        intro a c
        change C at c
        rw [RingHom.id_apply]
        change s (κ a * c) = s (κ a) * s c
        exact (s).map_mul _ _ }
  exact { hom' := f }

/-- 同じ標準環射を元A上の実single射へ移す。 -/
def deltaAlgebraPerfectionPDCompletionSingleMap :
    letI := pdCompletionCommRing C p (κ d)
    X ⟶ Y := by
  let := pdCompletionCommRing C p (κ d)
  exact boundedAboveDerivedSingleFunctor.map (deltaAlgebraPerfectionPDCompletionLinearMap E j d)

/-- 直接PD完備化H0の同じA作用付きsingleはp導来完備。 -/
theorem deltaAlgebraPerfectionPDCompletionSingle_isComplete_p :
    letI := pdCompletionCommRing C p (κ d)
    IsComplete A (p : A) (Y).obj := by
  let := pdCompletionCommRing C p (κ d)
  change IsModuleComplete A (p : A) (baseChangeScalarModule t)
  have h := pdCompletionH0_self_complete_p C p (κ d)
  rw [isModuleComplete_iff_recurrence_bijective] at h ⊢
  change Function.Bijective (fun z : ℕ → H => fun n => z n - t (p : A) * z (n + 1))
  change Function.Bijective (fun z : ℕ → H => fun n => z n - (p : H) * z (n + 1)) at h
  simpa only [map_natCast] using h

/-- 同じA作用付きsingleは元Aのdについても導来完備。 -/
theorem deltaAlgebraPerfectionPDCompletionSingle_isComplete_d :
    letI := pdCompletionCommRing C p (κ d)
    IsComplete A d (Y).obj := by
  let := pdCompletionCommRing C p (κ d)
  change IsModuleComplete A d (baseChangeScalarModule t)
  have h := pdCompletionH0_self_complete_d C p (κ d)
  rw [isModuleComplete_iff_recurrence_bijective] at h ⊢
  exact h

/-- 同じ標準single射を、実p完備化後から一意延長する。 -/
def deltaAlgebraPerfectionPDCompletionPMap :
    letI := pdCompletionCommRing C p (κ d)
    (Cp).obj X ⟶ Y := by
  let := pdCompletionCommRing C p (κ d)
  exact ObjectProperty.homMk
    ((derivedComplexCompletionHomEquiv A (p : A) (X).obj (Y).obj
      (deltaAlgebraPerfectionPDCompletionSingle_isComplete_p E j d)).symm
        (deltaAlgebraPerfectionPDCompletionSingleMap E j d).hom)

/-- p方向の一意延長は、元の実標準単位を保つ。 -/
theorem deltaAlgebraPerfectionPDCompletionPMap_unit :
    letI := pdCompletionCommRing C p (κ d)
    (Up).app X ≫ deltaAlgebraPerfectionPDCompletionPMap E j d =
      deltaAlgebraPerfectionPDCompletionSingleMap E j d := by
  let := pdCompletionCommRing C p (κ d)
  apply InducedCategory.hom_ext
  exact (derivedComplexCompletionHomEquiv A (p : A) (X).obj (Y).obj
    (deltaAlgebraPerfectionPDCompletionSingle_isComplete_p E j d)).apply_symm_apply
      (deltaAlgebraPerfectionPDCompletionSingleMap E j d).hom

/-- 実δ完全化の同じ実逐次対象から、直接PD完備化H0のsingleへの標準射。 -/
def deltaAlgebraPerfectionPDCompletionIteratedMap :
    letI := pdCompletionCommRing C p (κ d)
    DeltaAlgebraPerfectionIteratedPDCompletion E j d ⟶ Y := by
  let := pdCompletionCommRing C p (κ d)
  exact ObjectProperty.homMk
    ((derivedComplexCompletionHomEquiv A d ((Cp).obj X).obj (Y).obj
      (deltaAlgebraPerfectionPDCompletionSingle_isComplete_d E j d)).symm
        (deltaAlgebraPerfectionPDCompletionPMap E j d).hom)

/-- 両実標準単位の合成は、元の標準環射からのsingle射を保つ。 -/
theorem deltaAlgebraPerfectionPDCompletionIteratedMap_unit :
    letI := pdCompletionCommRing C p (κ d)
    ((Up).app X ≫ (Ud).app ((Cp).obj X)) ≫
        deltaAlgebraPerfectionPDCompletionIteratedMap E j d =
      deltaAlgebraPerfectionPDCompletionSingleMap E j d := by
  let := pdCompletionCommRing C p (κ d)
  have h : (Ud).app ((Cp).obj X) ≫ deltaAlgebraPerfectionPDCompletionIteratedMap E j d =
      deltaAlgebraPerfectionPDCompletionPMap E j d := by
    apply InducedCategory.hom_ext
    exact (derivedComplexCompletionHomEquiv A d ((Cp).obj X).obj (Y).obj
      (deltaAlgebraPerfectionPDCompletionSingle_isComplete_d E j d)).apply_symm_apply
        (deltaAlgebraPerfectionPDCompletionPMap E j d).hom
  rw [Category.assoc, h, deltaAlgebraPerfectionPDCompletionPMap_unit]

/-- 同じ両単位上で元の標準射に一致する延長は、この具体的標準延長だけである。 -/
theorem deltaAlgebraPerfectionPDCompletionIteratedMap_unique :
    letI := pdCompletionCommRing C p (κ d)
    ∀ g : DeltaAlgebraPerfectionIteratedPDCompletion E j d ⟶ Y,
      ((Up).app X ≫ (Ud).app ((Cp).obj X)) ≫ g =
        deltaAlgebraPerfectionPDCompletionSingleMap E j d →
      g = deltaAlgebraPerfectionPDCompletionIteratedMap E j d := by
  let := pdCompletionCommRing C p (κ d)
  intro g hg
  have he : (Up).app X ≫ ((Ud).app ((Cp).obj X) ≫ g) =
      (Up).app X ≫ ((Ud).app ((Cp).obj X) ≫
        deltaAlgebraPerfectionPDCompletionIteratedMap E j d) := by
    simpa only [Category.assoc] using
      hg.trans (deltaAlgebraPerfectionPDCompletionIteratedMap_unit E j d).symm
  apply InducedCategory.hom_ext
  apply derivedComplexCompletionHom_ext A d
    (deltaAlgebraPerfectionPDCompletionSingle_isComplete_d E j d)
  apply derivedComplexCompletionHom_ext A (p : A)
    (deltaAlgebraPerfectionPDCompletionSingle_isComplete_p E j d)
  exact congrArg (fun f => f.hom) he

end SerrePositivity.BhattScholze
