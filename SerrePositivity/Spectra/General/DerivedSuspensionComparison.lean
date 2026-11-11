module

public import SerrePositivity.Spectra.General.CircleSuspensionNaturality
public import SerrePositivity.HomotopicalAlgebra.Quillen.CofibrantComparison

/-! # Ordinary homotopy suspension versus derived circle tensor

The natural comparison on cofibrant spectra descends to the whole ordinary
homotopy category. The comparison works for any suspension coordinate K;
invertibility of circle tensor is not an input or a conclusion here.
-/

@[expose] public section
universe w u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Quillen

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {K : PointedSimplicialSet.{u}} [ModelCategory SSet.{u}]
  [spectrumModel : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)]
  [IsQuillenBifunctor (pointwiseTensorBifunctor (K := K))]
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)

include hcof in
lemma circleTensor_isLeftQuillen :
    IsLeftQuillen (pointwiseTensorFunctor (K := K) PointedSimplicialSet.circle) := by
  have : IsCofibrant PointedSimplicialSet.circle.{u} :=
    SimplicialModelInputs.pointedSimplicial_isCofibrant hcof _
  have : ∀ E : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K,
      ((pointwiseTensorBifunctor (K := K)).flip.obj E).IsLeftAdjoint :=
    fun E ↦ (mappingObjectAdjunction E).isLeftAdjoint
  exact isLeftQuillen_obj_of_cofibrant (pointwiseTensorBifunctor (K := K)) _

variable (hw : weakEquivalences SSet.{u} = SimplicialHomotopy.weakEquivalences)
  [IsLocallyPresentable.{w} (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)]
  (I J : MorphismProperty (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [MorphismProperty.IsStableUnderCobaseChangeAgainst
    (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
    (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))]
  {H : Type uH} [Category.{vH} H]
  (Q : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K ⥤ H)
  [Q.IsLocalization (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))]
  {LSigma : H ⥤ H}
  (γ : Q ⋙ LSigma ⟶ pointwiseTensorFunctor (K := K) PointedSimplicialSet.circle ⋙ Q)
  [LSigma.IsLeftDerivedFunctor γ
    (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))]

def derivedSuspensionComparisonIso : HomotopySuspension.localizedFunctor I J Q ≅ LSigma := by
  have := circleTensor_isLeftQuillen (K := K) hcof
  let ι : CofibrantObject (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K) ⥤
      GeneralSymmetricSpectrum PointedSimplicialSet.{u} K := CofibrantObject.ι
  let γc := Functor.whiskerLeft ι γ
  have : ∀ E, IsIso (γc.app E) := by
    intro E
    exact leftComparison_isIso Q Q γ E.obj
  have : IsIso γc := NatIso.isIso_of_isIso_app γc
  let e : (ι ⋙ Q) ⋙ HomotopySuspension.localizedFunctor I J Q ≅ (ι ⋙ Q) ⋙ LSigma :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ι (HomotopySuspension.localizationIso I J Q) ≪≫
      circleSuspensionCofibrantNatIso hcof hw I J Q ≪≫
      (asIso γc).symm ≪≫ (Functor.associator _ _ _).symm
  exact isoOfCofibrantComparison Q e

end SerrePositivity.GeneralSymmetricSpectrum
