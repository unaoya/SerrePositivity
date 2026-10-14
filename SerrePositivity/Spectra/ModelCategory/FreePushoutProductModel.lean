module

public import SerrePositivity.Spectra.ModelCategory.FreePushoutProduct
public import SerrePositivity.Spectra.ModelCategory.SimplicialLevel

/-! # Cofibration tests for pushout-products of two free spectra

The entire output arrow is compared with the sum-degree free image of the
source smash pushout-product. The source compatibility and the left Quillen
free functor prove the two generator tests, independently of HT-KQ.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
namespace SerrePositivity.SimplicialModelInputs
open SerrePositivity.Quillen
variable [ModelCategory SSet.{u}]
  (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
  (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)

lemma freePushoutProduct_cofibration (m n : ℕ)
    {A B X Y : PointedSimplicialSet.{u}} (i : A ⟶ B) (j : X ⟶ Y)
    [Cofibration i] [Cofibration j]
    (sp : (curriedTensor SymmetricSpectrum.{u}).PushoutObjObj
      ((SymmetricSpectrum.freeAt m).map i) ((SymmetricSpectrum.freeAt n).map j)) :
    let := simplicialLevelModelCategory hCof hFib
    Cofibration sp.ι := by
  let := simplicialLevelModelCategory hCof hFib
  let base := Functor.PushoutObjObj.ofHasPushout (curriedTensor PointedSimplicialSet.{u}) i j
  let : IsQuillenBifunctor (curriedTensor PointedSimplicialSet.{u}) :=
    (pointedSimplicial_monoidalModel hCof hFib).pushoutProduct
  have hc : Cofibration base.ι :=
    IsQuillenBifunctor.cofibration i j base inferInstance inferInstance
  have hf := (simplicialLevel_freeAt_isLeftQuillen hCof hFib (m + n)).map_cofibrations
    base.ι ((cofibration_iff _).1 hc)
  exact (cofibration_iff _).2
    (((cofibrations SymmetricSpectrum.{u}).arrow_mk_iso_iff
      (SymmetricSpectrum.freePushoutProductIso m n i j base sp)).2 hf)

lemma freePushoutProduct_trivialCofibration (m n : ℕ)
    {A B X Y : PointedSimplicialSet.{u}} (i : A ⟶ B) (j : X ⟶ Y)
    [Cofibration i] [Cofibration j] (hw : WeakEquivalence i ∨ WeakEquivalence j)
    (sp : (curriedTensor SymmetricSpectrum.{u}).PushoutObjObj
      ((SymmetricSpectrum.freeAt m).map i) ((SymmetricSpectrum.freeAt n).map j)) :
    let := simplicialLevelModelCategory hCof hFib
    trivialCofibrations SymmetricSpectrum.{u} sp.ι := by
  let := simplicialLevelModelCategory hCof hFib
  let base := Functor.PushoutObjObj.ofHasPushout (curriedTensor PointedSimplicialSet.{u}) i j
  let : IsQuillenBifunctor (curriedTensor PointedSimplicialSet.{u}) :=
    (pointedSimplicial_monoidalModel hCof hFib).pushoutProduct
  have hc : Cofibration base.ι :=
    IsQuillenBifunctor.cofibration i j base inferInstance inferInstance
  have he : WeakEquivalence base.ι :=
    IsQuillenBifunctor.weakEquivalence i j base inferInstance inferInstance hw
  have hf := (simplicialLevel_freeAt_isLeftQuillen hCof hFib (m + n)).map_trivialCofibrations
    base.ι ((mem_trivialCofibrations_iff _).2 ⟨hc, he⟩)
  exact ((trivialCofibrations SymmetricSpectrum.{u}).arrow_mk_iso_iff
    (SymmetricSpectrum.freePushoutProductIso m n i j base sp)).2 hf

end SerrePositivity.SimplicialModelInputs
