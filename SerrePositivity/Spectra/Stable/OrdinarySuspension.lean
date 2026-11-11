module

public import SerrePositivity.Spectra.General.DerivedSuspensionComparison
public import SerrePositivity.Spectra.General.SimplicialSuspensionComparison
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedAdjunction

/-! # Ordinary suspension with the derived existing loop functor as inverse

The ordinary homotopy-pushout suspension is transported through the proved
natural comparison to the derived existing suspension/loop adjunction.
Invertibility of derived circle tensor is a separate input of this
transport theorem, supplied by the constructed K-local model for K = S¹.
-/

@[expose] public section
universe w u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Quillen

namespace SerrePositivity.SymmetricSpectrum
variable [ModelCategory SSet.{u}] [spectrumModel : ModelCategory SymmetricSpectrum.{u}]

local instance generalSpectrumModel : ModelCategory (GeneralSymmetricSpectrum
    PointedSimplicialSet.{u} PointedSimplicialSet.circle.{u}) := spectrumModel

local instance nativeZero : HasZeroObject SymmetricSpectrum.{u} :=
  inferInstanceAs (HasZeroObject
    (GeneralSymmetricSpectrum PointedSimplicialSet.{u} PointedSimplicialSet.circle.{u}))

local instance nativeZeroMorphisms : HasZeroMorphisms SymmetricSpectrum.{u} :=
  inferInstanceAs (HasZeroMorphisms
    (GeneralSymmetricSpectrum PointedSimplicialSet.{u} PointedSimplicialSet.circle.{u}))

variable
  [IsQuillenBifunctor (GeneralSymmetricSpectrum.pointwiseTensorBifunctor
    (C := PointedSimplicialSet.{u}) (K := PointedSimplicialSet.circle.{u}))]
  [lp : IsLocallyPresentable.{w} SymmetricSpectrum.{u}]
  (I J : MorphismProperty SymmetricSpectrum.{u})
  [generation : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [proper : (weakEquivalences SymmetricSpectrum.{u}).IsStableUnderCobaseChangeAgainst
    (cofibrations SymmetricSpectrum.{u})]
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{u} = SimplicialHomotopy.weakEquivalences)
  {H : Type uH} [Category.{vH} H] (Q : SymmetricSpectrum.{u} ⥤ H)
  [hQ : Q.IsLocalization (weakEquivalences SymmetricSpectrum.{u})]
  {LSigma ROmega : H ⥤ H}
  (γ : Q ⋙ LSigma ⟶ suspensionFunctor ⋙ Q)
  [hγ : LSigma.IsLeftDerivedFunctor γ (weakEquivalences SymmetricSpectrum.{u})]
  (ρ : loopFunctor ⋙ Q ⟶ Q ⋙ ROmega)
  [hρ : ROmega.IsRightDerivedFunctor ρ (weakEquivalences SymmetricSpectrum.{u})]

def ordinarySuspensionLoopEquivalence (hSigma : LSigma.IsEquivalence) : H ≌ H := by
  have : IsLeftQuillen suspensionFunctor.{u} :=
    GeneralSymmetricSpectrum.circleTensor_isLeftQuillen hcof
  have := isRightQuillen_of_isLeftQuillen suspensionLoopAdjunction.{u}
  have : LSigma.IsEquivalence := hSigma
  let n := (derivedAdjunction Q Q suspensionLoopAdjunction γ ρ).toEquivalence
  have : Q.IsLocalization (weakEquivalences
      (GeneralSymmetricSpectrum PointedSimplicialSet.{u} PointedSimplicialSet.circle.{u})) := hQ
  have : LSigma.IsLeftDerivedFunctor γ (weakEquivalences
      (GeneralSymmetricSpectrum PointedSimplicialSet.{u} PointedSimplicialSet.circle.{u})) := hγ
  have : IsLocallyPresentable.{w}
      (GeneralSymmetricSpectrum PointedSimplicialSet.{u} PointedSimplicialSet.circle.{u}) := lp
  have : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w}
      (C := GeneralSymmetricSpectrum
        PointedSimplicialSet.{u} PointedSimplicialSet.circle.{u}) I J :=
    generation
  have : MorphismProperty.IsStableUnderCobaseChangeAgainst
      (weakEquivalences (GeneralSymmetricSpectrum
        PointedSimplicialSet.{u} PointedSimplicialSet.circle.{u}))
      (cofibrations (GeneralSymmetricSpectrum
        PointedSimplicialSet.{u} PointedSimplicialSet.circle.{u})) :=
    proper
  let e := GeneralSymmetricSpectrum.derivedSuspensionComparisonIso hcof hw I J Q γ
  exact CategoryTheory.Equivalence.mk (HomotopySuspension.localizedFunctor I J Q) ROmega
    ((Functor.isoWhiskerRight e ROmega ≪≫ n.unitIso.symm).symm)
    (Functor.isoWhiskerLeft ROmega e ≪≫ n.counitIso)

end SerrePositivity.SymmetricSpectrum
