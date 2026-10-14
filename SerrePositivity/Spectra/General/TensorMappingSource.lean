module

public import SerrePositivity.Spectra.General.TensorMappingObject
public import SerrePositivity.CategoryTheory.Monoidal.ActionComparisonNaturality

/-! # Source naturality of C-valued tensor mapping representability -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

/-- Changing the spectrum source respects the composite power adjunction. -/
lemma tensorMappingPowerAdjunction_naturality_source (X Z : C)
    {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor (Z ⊗ X) E' ⟶ F) :
    (tensorMappingPowerAdjunction X E).homEquiv Z F
        ((pointwiseTensorFunctor (Z ⊗ X)).map f ≫ g) =
      (tensorMappingPowerAdjunction X E').homEquiv Z F g ≫
        (ihom X).map ((mappingObjectBifunctor.map f.op).app F) := by
  unfold tensorMappingPowerAdjunction
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change (((ihom.adjunction X).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight X)).homEquiv Z _)
      (mappingObjectHomEquiv (Z ⊗ X) E F
        ((pointwiseTensorFunctor (Z ⊗ X)).map f ≫ g)) = _
  rw [mappingObjectHomEquiv_naturality_source]
  exact ((ihom.adjunction X).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight X)).homEquiv_naturality_right _ _

/-- Tensor mapping-object comparison is contravariantly natural in the source. -/
lemma tensorMappingIso_naturality_source (X : C)
    {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) :
    (mappingObjectBifunctor.map ((pointwiseTensorFunctor X).map f).op).app F ≫
        (tensorMappingIso X E F).hom =
      (tensorMappingIso X E' F).hom ≫ (ihom X).map ((mappingObjectBifunctor.map f.op).app F) := by
  apply ActionComparisonNaturality.parameter
    (mappingObjectAdjunction (pointwiseTensor X E))
    (mappingObjectAdjunction (pointwiseTensor X E'))
    (tensorMappingPowerAdjunction X E) (tensorMappingPowerAdjunction X E')
    (tensorMappingParameterIso X E).symm (tensorMappingParameterIso X E').symm
    (fun Z ↦ (pointwiseTensorFunctor Z).map ((pointwiseTensorFunctor X).map f))
    (fun Y ↦ (mappingObjectBifunctor.map ((pointwiseTensorFunctor X).map f).op).app Y)
    (fun Z ↦ (pointwiseTensorFunctor (Z ⊗ X)).map f)
    (fun Y ↦ (ihom X).map ((mappingObjectBifunctor.map f.op).app Y))
  · intro Z Y g
    exact mappingObjectHomEquiv_naturality_source Z ((pointwiseTensorFunctor X).map f) Y g
  · intro Z Y g
    exact tensorMappingPowerAdjunction_naturality_source X Z f Y g
  · intro Z
    change (pointwiseTensorFunctor Z).map ((pointwiseTensorFunctor X).map f) ≫
        (pointwiseTensorAssociator Z X E').inv =
      (pointwiseTensorAssociator Z X E).inv ≫ (pointwiseTensorFunctor (Z ⊗ X)).map f
    apply (cancel_mono (pointwiseTensorAssociator Z X E').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [pointwiseTensorAssociator_naturality]
    simp only [Iso.inv_hom_id_assoc]

/-- The tensor mapping comparison is natural in both spectrum variables. -/
def tensorMappingBifunctorIso (X : C) :
    (pointwiseTensorFunctor (K := K) X).op ⋙ mappingObjectBifunctor ≅
      mappingObjectBifunctor ⋙ (Functor.whiskeringRight _ _ _).obj (ihom X) :=
  NatIso.ofComponents (fun E ↦ tensorMappingNatIso X E.unop) (fun f ↦ by
    apply NatTrans.ext
    funext F
    exact tensorMappingIso_naturality_source X f.unop F)

end SerrePositivity.GeneralSymmetricSpectrum
