module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSourceNonpositive
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0Comparison

/-! # 元の実根添加源の逐次完備化と同じaugmentationのH0比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d

/-- 元の実係数源のp,d逐次実完備化も非正である。 -/
theorem deltaRootSourceIteratedPDCompletion_isLE_zero :
    (DeltaRootSourceIteratedPDCompletion D d b).obj.IsLE 0 := by
  apply DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A d _ 0
  exact DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
    (deltaRootSourceCoefficient_isLE_zero D d b)

/-- raw係数対象の同じp,d逐次実完備化も非正である。 -/
theorem deltaRootSourceRawIteratedCompletion_isLE_zero :
    (DeltaRootSourceRawIteratedCompletion D d b).obj.IsLE 0 := by
  apply DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A d _ 0
  exact DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
    (deltaRootSourceRawCoefficient_isLE_zero D d b)

/-- 同じ元のaugmentationは、実p完備化後にもH0同型を誘導する。 -/
theorem deltaRootSourceRawPComparison_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (((Cp).map (deltaRootSourceRawCoefficientAugmentation D d b)).hom)) := by
  exact DerivedCompletion.boundedAboveDerivedCompletion_h0_map_isIso A (p : A)
    (deltaRootSourceRawCoefficientAugmentation D d b)
    (deltaRootSourceCoefficient_isLE_zero D d b)
    (deltaRootSourceRawCoefficient_isLE_zero D d b)
    (deltaRootSourceRawCoefficientAugmentation_h0_isIso D d b)

/-- 既存の標準逐次完備化比較射そのものがH0同型を誘導する。 -/
theorem deltaRootSourceRawIteratedComparison_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (deltaRootSourceRawIteratedComparison D d b).hom) := by
  exact DerivedCompletion.boundedAboveDerivedCompletion_h0_map_isIso A d
    ((Cp).map (deltaRootSourceRawCoefficientAugmentation D d b))
    (DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (deltaRootSourceCoefficient_isLE_zero D d b))
    (DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (deltaRootSourceRawCoefficient_isLE_zero D d b))
    (deltaRootSourceRawPComparison_h0_isIso D d b)

/-- 実逐次源のH0とrawの実逐次完備化のH0を、同じ標準比較射で同定する。 -/
def deltaRootSourceRawIteratedH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (DeltaRootSourceIteratedPDCompletion D d b).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (DeltaRootSourceRawIteratedCompletion D d b).obj := by
  let := deltaRootSourceRawIteratedComparison_h0_isIso D d b
  exact asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (deltaRootSourceRawIteratedComparison D d b).hom)

end SerrePositivity.BhattScholze
