module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionCompletionResidue
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion

/-! # 実δ完全化の逐次完備化と正確な係数制限の比較 -/

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
local notation "C∞" => DeltaPerfection E
local notation "κ∞" => deltaAlgebraPerfectionCoefficient E j
local notation "R∞" => boundedAboveDerivedRestrictScalars κ∞
local notation "S∞" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (ModuleCat.of C∞ C∞)
local notation "X∞" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule κ∞)
local notation "Cp" => boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => boundedAboveDerivedCompletionFunctor A d
local notation "Up" => boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => boundedAboveDerivedCompletionUnit A d
local notation "Cp∞" => boundedAboveDerivedCompletionFunctor C∞ (κ∞ (p : A))
local notation "Cd∞" => boundedAboveDerivedCompletionFunctor C∞ (κ∞ d)
local notation "Up∞" => boundedAboveDerivedCompletionUnit C∞ (κ∞ (p : A))
local notation "Ud∞" => boundedAboveDerivedCompletionUnit C∞ (κ∞ d)

/-- 元のC上のsingleの係数制限は、正確なA作用を持つ既存のsingleと同型。 -/
def deltaAlgebraPerfectionSingleRestrictionIso : (R∞).obj S∞ ≅ X∞ :=
  ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso κ∞ 0).app (ModuleCat.of C∞ C∞))

/-- 共通G8を両方向へ適用した、同じ実逐次完備化対象の比較。 -/
def deltaAlgebraPerfectionCompletionRestrictionIso :
    DeltaAlgebraPerfectionIteratedPDCompletion E j d ≅
      (R∞).obj ((Cd∞).obj ((Cp∞).obj S∞)) :=
  (Cd).mapIso ((Cp).mapIso (deltaAlgebraPerfectionSingleRestrictionIso E j).symm ≪≫
      (boundedAboveCompletionRestrictionIso κ∞ (p : A)).app S∞) ≪≫
    (boundedAboveCompletionRestrictionIso κ∞ d).app ((Cp∞).obj S∞)

/-- 逐次G8比較は、元の両完備化単位の合成を保つ。 -/
theorem deltaAlgebraPerfectionCompletionRestrictionIso_unit :
    (((Up).app X∞) ≫ (Ud).app ((Cp).obj X∞)) ≫
        (deltaAlgebraPerfectionCompletionRestrictionIso E j d).hom =
      (deltaAlgebraPerfectionSingleRestrictionIso E j).inv ≫
        (R∞).map (((Up∞).app S∞) ≫ (Ud∞).app ((Cp∞).obj S∞)) := by
  let e := (Cp).mapIso (deltaAlgebraPerfectionSingleRestrictionIso E j).symm ≪≫
    (boundedAboveCompletionRestrictionIso κ∞ (p : A)).app S∞
  have hp : (Up).app X∞ ≫ e.hom =
      (deltaAlgebraPerfectionSingleRestrictionIso E j).inv ≫
        (R∞).map ((Up∞).app S∞) := by
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
    rw [← Category.assoc, ← (Up).naturality]
    simp only [Functor.id_map, Category.assoc]
    rw [boundedAboveCompletionRestrictionIso_unit]
  have hn := (Ud).naturality e.hom
  simp only [Functor.id_map] at hn
  change ((Up).app X∞ ≫ (Ud).app ((Cp).obj X∞)) ≫
    ((Cd).map e.hom ≫ (boundedAboveCompletionRestrictionIso κ∞ d).hom.app _) = _
  calc
    _ = (Up).app X∞ ≫
        (((Ud).app ((Cp).obj X∞) ≫ (Cd).map e.hom) ≫
          (boundedAboveCompletionRestrictionIso κ∞ d).hom.app _) := by
      simp only [Category.assoc]
    _ = ((Up).app X∞ ≫ e.hom) ≫
        ((Ud).app ((R∞).obj ((Cp∞).obj S∞)) ≫
          (boundedAboveCompletionRestrictionIso κ∞ d).hom.app _) := by
      rw [← hn]
      simp only [Category.assoc, Functor.comp_obj]
    _ = _ := by
      rw [hp, boundedAboveCompletionRestrictionIso_unit, Functor.map_comp]
      simp only [Category.assoc]

/-- 同じ実逐次対象のH0も、元のκ作用を保ったC上のH0の制限と同型。 -/
def deltaAlgebraPerfectionCompletionRestrictionH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (DeltaAlgebraPerfectionIteratedPDCompletion E j d).obj ≅
      (ModuleCat.restrictScalars κ∞).obj
        ((DerivedCategory.homologyFunctor (ModuleCat C∞) 0).obj
          ((Cd∞).obj ((Cp∞).obj S∞)).obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaAlgebraPerfectionCompletionRestrictionIso E j d)) ≪≫
    (derivedRestrictScalarsHomologyIso κ∞ 0).app (((Cd∞).obj ((Cp∞).obj S∞)).obj)

end SerrePositivity.BhattScholze
