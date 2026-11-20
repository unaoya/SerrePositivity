module

public import SerrePositivity.Spectra.General.SimplicialCylinder
public import SerrePositivity.HomotopicalAlgebra.Pointed.HomotopySuspension

/-! # Comparing the actual circle tensor with the ordinary suspension homotopy pushout

For a cofibrant spectrum the good-cylinder quotient comparison identifies
circle tensor with the homotopy colimit of zero <- E -> zero in any ordinary
localization. This is an objectwise comparison; naturality and comparison
of the resulting functors on the homotopy category are separate obligations.
-/

@[expose] public section
universe w u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Quillen
open scoped ZeroObject

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {K : PointedSimplicialSet.{u}}
  [ModelCategory SSet.{u}]
  [spectrumModel : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)]
  [IsQuillenBifunctor (pointwiseTensorBifunctor (K := K))]
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{u} = SimplicialHomotopy.weakEquivalences)
  (E : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K) [IsCofibrant E]

lemma circleTensor_zeroCylinder_isPushout :
    IsPushout (simplicialCylinder hcof hw E).i
      (0 : E ⨿ E ⟶ (0 : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
      (circleTensorQuotient E) (0 : (0 : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K) ⟶
        pointwiseTensor PointedSimplicialSet.circle E) := by
  apply (circleTensor_cylinder_isPushout hcof hw E).of_iso
    (Iso.refl _) (Iso.refl _) (circleTensorPoint_isZero E).isoZero (Iso.refl _)
  all_goals simp

variable [IsLocallyPresentable.{w} (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)]
  (I J : MorphismProperty (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [MorphismProperty.IsStableUnderCobaseChangeAgainst
    (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
    (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))]
  {H : Type uH} [Category.{vH} H]
  (Q : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K ⥤ H)
  [Q.IsLocalization (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))]

def circleHomotopySuspensionIso :
    Q.obj ((HomotopySuspension.functor I J).obj E) ≅
      Q.obj (pointwiseTensor PointedSimplicialSet.circle E) := by
  have := simplicialIntervalCylinder_isGood hcof hw E
  have : (simplicialCylinder hcof hw E).IsGood :=
    ModelCylinder.changeBase_isGood (simplicialIntervalCylinder hcof hw E) (simplicialVertexIso E)
  exact HomotopySuspension.cylinderQuotientIso I J Q (simplicialCylinder hcof hw E)
    (circleTensorQuotient E) (circleTensor_zeroCylinder_isPushout hcof hw E)

end SerrePositivity.GeneralSymmetricSpectrum
