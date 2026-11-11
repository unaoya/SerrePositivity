module

public import SerrePositivity.Spectra.Stable.TensorInverseMap
public import SerrePositivity.Spectra.Stable.EnrichedModel
public import SerrePositivity.HomotopicalAlgebra.Monoidal.DerivedTensorInverse

/-! # Derived K-tensor invertibility in the constructed spectral localization

The inverse is the left derived functor of tensoring with F₁(1). The actual
evaluation is proved weak independently, and the localized monoidal model is
supplied by the existing construction. This does not identify K with the
ordinary suspension coordinate.
-/

@[expose] public section
universe w v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.Quillen
open SerrePositivity.ModelGeneration SerrePositivity.SpectrumLevelModel

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [ModelCategory C] [IsQuillenBifunctor (curriedTensor C)] (K : C) [IsCofibrant K]
  [IsCofibrant (𝟙_ C)] [levelModel : ModelCategory (GeneralSymmetricSpectrum C K)]
  [∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n)]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J)]
  [ModelCategory SSet.{v}]
  (cofC : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (cofSp : MorphismProperty.FunctorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K)))
  (fibSp : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K)))
  (p : StableModelPresentation.{w} K cofSp fibSp (levelGenerators K I))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hdom : ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A)
  {H : Type uH} [Category.{vH} H]
  (Q : GeneralSymmetricSpectrum C K ⥤ H)
  [hQ : Q.IsLocalization p.localization.model.categoryWithWeakEquivalences.weakEquivalences]
  {LK LI : H ⥤ H}
  (α : Q ⋙ LK ⟶ tensorLeft ((freeAt (K := K) 0).obj K) ⋙ Q)
  (β : Q ⋙ LI ⟶ tensorLeft ((freeAt (K := K) 1).obj (𝟙_ C)) ⋙ Q)
  [hα : LK.IsLeftDerivedFunctor α
    p.localization.model.categoryWithWeakEquivalences.weakEquivalences]
  [hβ : LI.IsLeftDerivedFunctor β
    p.localization.model.categoryWithWeakEquivalences.weakEquivalences]

include Q α β hQ hα hβ in
def StableModelPresentation.derivedTensorInverseEquivalence : H ≌ H := by
  have hM := p.monoidal_model K I J cofSp fibSp hcof hfib hdom
  have he := p.tensorInverseEvaluation_isWeakEquivalence K cofC cofSp fibSp _ hcof hfib
  have := (freeAtAdjunction (K := K) 0).isLeftAdjoint
  have := (freeAtAdjunction (K := K) 1).isLeftAdjoint
  have h0 := map_isCofibrant (freeAt (K := K) 0) K
  have h1 := map_isCofibrant (freeAt (K := K) 1) (𝟙_ C)
  have hu := general_levelUnit_isCofibrant K
  have hc0 := (cofibration_iff _).mp h0
  have hc1 := (cofibration_iff _).mp h1
  have hcu := (cofibration_iff _).mp hu
  have nc0 := p.localization.cofibrations_eq.symm.le _ hc0
  have nc1 := p.localization.cofibrations_eq.symm.le _ hc1
  have ncu := p.localization.cofibrations_eq.symm.le _ hcu
  letI stableModel : ModelCategory (GeneralSymmetricSpectrum C K) := p.localization.model
  have : Q.IsLocalization (weakEquivalences (GeneralSymmetricSpectrum C K)) := hQ
  have : LK.IsLeftDerivedFunctor α (weakEquivalences (GeneralSymmetricSpectrum C K)) := hα
  have : LI.IsLeftDerivedFunctor β (weakEquivalences (GeneralSymmetricSpectrum C K)) := hβ
  have : @MonoidalModelCategory (GeneralSymmetricSpectrum C K) _ stableModel _ := hM
  have : @IsCofibrant (GeneralSymmetricSpectrum C K) _
      stableModel.categoryWithCofibrations _ ((freeAt (K := K) 0).obj K) :=
    ⟨nc0⟩
  have : @IsCofibrant (GeneralSymmetricSpectrum C K) _
      stableModel.categoryWithCofibrations _ ((freeAt (K := K) 1).obj (𝟙_ C)) :=
    ⟨nc1⟩
  have : @IsCofibrant (GeneralSymmetricSpectrum C K) _
      stableModel.categoryWithCofibrations _ (𝟙_ (GeneralSymmetricSpectrum C K)) :=
    ⟨ncu⟩
  have : WeakEquivalence (tensorInverseEvaluation K) := ⟨he⟩
  let e := (β_ ((freeAt (K := K) 0).obj K) ((freeAt (K := K) 1).obj (𝟙_ C))).hom ≫
    tensorInverseEvaluation K
  have : WeakEquivalence e := inferInstanceAs (WeakEquivalence (_ ≫ tensorInverseEvaluation K))
  exact Quillen.derivedTensorInverseEquivalence (model := stableModel) Q α β e

include K I J cofC cofSp fibSp p hcof hfib hdom Q α β in
lemma StableModelPresentation.derived_tensor_isEquivalence : LK.IsEquivalence :=
  (p.derivedTensorInverseEquivalence K I J cofC cofSp fibSp hcof hfib hdom
    (Q := Q) (α := α) (β := β)).isEquivalence_functor

variable {LP : H ⥤ H} (γ : Q ⋙ LP ⟶ pointwiseTensorFunctor K ⋙ Q)
  [hγ : LP.IsLeftDerivedFunctor γ
    p.localization.model.categoryWithWeakEquivalences.weakEquivalences]

include K I J cofC cofSp fibSp p hcof hfib hdom Q α β γ in
lemma StableModelPresentation.derived_pointwiseTensor_isEquivalence : LP.IsEquivalence := by
  have := p.derived_tensor_isEquivalence K I J cofC cofSp fibSp hcof hfib hdom Q α β
  let e : LK ≅ LP := Functor.leftDerivedNatIso LK LP α γ
    p.localization.model.categoryWithWeakEquivalences.weakEquivalences
    (Functor.isoWhiskerRight (tensorFreeZeroPointwiseNatIso K) Q)
  exact Functor.isEquivalence_of_iso e

variable {RP : H ⥤ H} (ρ : cotensorFunctor K ⋙ Q ⟶ Q ⋙ RP)
  [hρ : RP.IsRightDerivedFunctor ρ
    p.localization.model.categoryWithWeakEquivalences.weakEquivalences]

include Q α β γ ρ hQ hα hβ hγ hρ in
def StableModelPresentation.derivedTensorCotensorEquivalence : H ≌ H := by
  have := general_levelTensor_isQuillen K I J
  have hP := p.derived_pointwiseTensor_isEquivalence
    K I J cofC cofSp fibSp hcof hfib hdom Q α β γ
  have hT := p.pointwiseTensor_isLeftQuillen K cofSp fibSp _ hcof hfib K
  letI stableModel : ModelCategory (GeneralSymmetricSpectrum C K) := p.localization.model
  have : Q.IsLocalization (weakEquivalences (GeneralSymmetricSpectrum C K)) := hQ
  have : LP.IsLeftDerivedFunctor γ (weakEquivalences (GeneralSymmetricSpectrum C K)) := hγ
  have : RP.IsRightDerivedFunctor ρ (weakEquivalences (GeneralSymmetricSpectrum C K)) := hρ
  have : IsLeftQuillen (pointwiseTensorFunctor K) := hT
  have := isRightQuillen_of_isLeftQuillen (pointwiseTensorCotensorAdjunction (K := K) K)
  have : LP.IsEquivalence := hP
  exact (derivedAdjunction Q Q (pointwiseTensorCotensorAdjunction (K := K) K) γ ρ).toEquivalence

include Q hQ in
def StableModelPresentation.canonicalDerivedKTensorEquivalence : H ≌ H := by
  have := general_levelTensor_isQuillen K I J
  have hT0 := p.freeTensor_isLeftQuillen K cofSp fibSp _ hcof hfib 0 K
  have hT1 := p.freeTensor_isLeftQuillen K cofSp fibSp _ hcof hfib 1 (𝟙_ C)
  let W := p.localization.model.categoryWithWeakEquivalences.weakEquivalences
  letI stableModel : ModelCategory (GeneralSymmetricSpectrum C K) := p.localization.model
  have : Q.IsLocalization (weakEquivalences (GeneralSymmetricSpectrum C K)) := hQ
  have : IsLeftQuillen (tensorLeft ((freeAt (K := K) 0).obj K)) := hT0
  have : IsLeftQuillen (tensorLeft ((freeAt (K := K) 1).obj (𝟙_ C))) := hT1
  have : (tensorLeft ((freeAt (K := K) 0).obj K) ⋙ Q).HasPointwiseLeftDerivedFunctor W :=
    @Quillen.hasPointwiseLeftDerivedFunctor _ _ stableModel _ _ stableModel _ _ Q hQ _ hT0
  have : (tensorLeft ((freeAt (K := K) 1).obj (𝟙_ C)) ⋙ Q).HasPointwiseLeftDerivedFunctor W :=
    @Quillen.hasPointwiseLeftDerivedFunctor _ _ stableModel _ _ stableModel _ _ Q hQ _ hT1
  exact p.derivedTensorInverseEquivalence (levelModel := levelModel)
    K I J cofC cofSp fibSp hcof hfib hdom
    (Q := Q)
    (α := (tensorLeft ((freeAt (K := K) 0).obj K) ⋙ Q).totalLeftDerivedCounit Q W)
    (β := (tensorLeft ((freeAt (K := K) 1).obj (𝟙_ C)) ⋙ Q).totalLeftDerivedCounit Q W)
    (hα := by infer_instance) (hβ := by infer_instance)

end SerrePositivity.SpectrumStabilization
