module

public import SerrePositivity.Spectra.General.SuspensionPushout
public import SerrePositivity.Spectra.General.ParametrizedMapping
public import SerrePositivity.Spectra.ModelCategory.SimplicialMonoidal
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.QuillenCylinder
public import SerrePositivity.HomotopicalAlgebra.Monoidal.QuillenBifunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # A good simplicial interval cylinder for a cofibrant general spectrum

The coordinate K remains arbitrary. The actual pointed action being
Quillen is the only compatibility used, so this applies to the localized
action already constructed in S2. The underlying interval, endpoints and
collapse are images under free-basepoint addition and parameter tensor.
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {K : PointedSimplicialSet.{u}}
  [ModelCategory SSet.{u}] [ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)]
  [IsQuillenBifunctor (pointwiseTensorBifunctor (K := K))]
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{u} = SimplicialHomotopy.weakEquivalences)
  (E : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K) [IsCofibrant E]

abbrev simplicialParameterFunctor :
    SSet.{u} ⥤ GeneralSymmetricSpectrum PointedSimplicialSet.{u} K :=
  PointedObject.adjoinFunctor ⋙ mappingTensorFunctor E

lemma simplicialParameter_isLeftQuillen : IsLeftQuillen (simplicialParameterFunctor E) := by
  have := PointedModel.adjoin_isLeftQuillen (C := SSet.{u})
  have : ∀ X : PointedSimplicialSet.{u},
      ((pointwiseTensorBifunctor (K := K)).flip.flip.obj X).IsLeftAdjoint :=
    fun X ↦ (pointwiseTensorCotensorAdjunction (K := K) X).isLeftAdjoint
  have : IsLeftQuillen (mappingTensorFunctor E) :=
    isLeftQuillen_obj_of_cofibrant (pointwiseTensorBifunctor (K := K)).flip E
  exact isLeftQuillen_comp _ _

def simplicialVertexIso :
    (simplicialParameterFunctor E).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ≅ E :=
  (mappingTensorFunctor E).mapIso
    (PointedObject.adjoinFunctor.mapIso QuillenStandardFrame.zeroUnitIso) ≪≫
      pointwiseTensorUnitNatIso.app E

def simplicialIntervalCylinder :
    Cylinder ((simplicialParameterFunctor E).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0))) := by
  have := (PointedObject.adjoinForgetAdjunction (C := SSet.{u})).isLeftAdjoint
  have := (mappingObjectAdjunction E).isLeftAdjoint
  have := simplicialParameter_isLeftQuillen E
  exact QuillenStandardFrame.cylinder (simplicialParameterFunctor E) hcof hw

lemma simplicialIntervalCylinder_isGood : (simplicialIntervalCylinder hcof hw E).IsGood := by
  have := (PointedObject.adjoinForgetAdjunction (C := SSet.{u})).isLeftAdjoint
  have := (mappingObjectAdjunction E).isLeftAdjoint
  have := simplicialParameter_isLeftQuillen E
  exact QuillenStandardFrame.cylinder_isGood (simplicialParameterFunctor E) hcof hw

include hcof in
lemma intervalBoundaryTensorMap_cofibration : Cofibration (intervalBoundaryTensorMap E) := by
  have : Cofibration (SSet.boundary.{u} 1).ι := by
    constructor
    rw [hcof]
    infer_instance
  have := simplicialParameter_isLeftQuillen E
  exact map_cofibration (simplicialParameterFunctor E) (SSet.boundary.{u} 1).ι

def simplicialCylinder : Cylinder E :=
  ModelCylinder.changeBase (simplicialIntervalCylinder hcof hw E) (simplicialVertexIso E)

abbrev intervalBoundaryCofan : BinaryCofan E E :=
  BinaryCofan.mk
    ((simplicialVertexIso E).inv ≫
      (simplicialParameterFunctor E).map (SSet.boundary.ι.{u} (1 : Fin 2)))
    ((simplicialVertexIso E).inv ≫
      (simplicialParameterFunctor E).map (SSet.boundary.ι.{u} (0 : Fin 2)))

def intervalBoundaryCofanIsColimit : IsColimit (intervalBoundaryCofan E) := by
  have := (PointedObject.adjoinForgetAdjunction (C := SSet.{u})).isLeftAdjoint
  have := (mappingObjectAdjunction E).isLeftAdjoint
  have h := mapIsColimitOfPreservesOfIsColimit (simplicialParameterFunctor E) _ _
    BoundaryOne.isColimit
  exact BinaryCofan.isColimitCompRightIso _ (simplicialVertexIso E).inv
    (BinaryCofan.isColimitCompLeftIso _ (simplicialVertexIso E).inv h)

def intervalBoundaryCoproductIso : E ⨿ E ≅ (intervalBoundaryCofan E).pt :=
  (coprodIsCoprod E E).coconePointUniqueUpToIso (intervalBoundaryCofanIsColimit E)

lemma intervalBoundaryCoproductIso_inclusion :
    (intervalBoundaryCoproductIso E).hom ≫ intervalBoundaryTensorMap E =
      (simplicialCylinder hcof hw E).i := by
  apply coprod.hom_ext
  · have h := IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod E E)
      (intervalBoundaryCofanIsColimit E) (Discrete.mk WalkingPair.left)
    change coprod.inl ≫ (intervalBoundaryCoproductIso E).hom =
      (intervalBoundaryCofan E).inl at h
    rw [← Category.assoc, h]
    change ((simplicialVertexIso E).inv ≫
      (simplicialParameterFunctor E).map (SSet.boundary.ι (1 : Fin 2))) ≫
        (simplicialParameterFunctor E).map (SSet.boundary.{u} 1).ι = _
    rw [Category.assoc, ← Functor.map_comp, SSet.boundary.ι_ι]
    simp [simplicialCylinder, ModelCylinder.changeBase, simplicialIntervalCylinder,
      QuillenStandardFrame.cylinder, cosimplicialCylinder, Precylinder.i]
    rfl
  · have h := IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod E E)
      (intervalBoundaryCofanIsColimit E) (Discrete.mk WalkingPair.right)
    change coprod.inr ≫ (intervalBoundaryCoproductIso E).hom =
      (intervalBoundaryCofan E).inr at h
    rw [← Category.assoc, h]
    change ((simplicialVertexIso E).inv ≫
      (simplicialParameterFunctor E).map (SSet.boundary.ι (0 : Fin 2))) ≫
        (simplicialParameterFunctor E).map (SSet.boundary.{u} 1).ι = _
    rw [Category.assoc, ← Functor.map_comp, SSet.boundary.ι_ι]
    simp [simplicialCylinder, ModelCylinder.changeBase, simplicialIntervalCylinder,
      QuillenStandardFrame.cylinder, cosimplicialCylinder, Precylinder.i]
    rfl

lemma circleTensor_cylinder_isPushout : IsPushout (simplicialCylinder hcof hw E).i
    (0 : E ⨿ E ⟶ (mappingTensorFunctor E).obj PointedObject.point)
    (circleTensorQuotient E) (0 : _ ⟶ pointwiseTensor PointedSimplicialSet.circle E) := by
  apply (circleTensor_isPushout E).of_iso (intervalBoundaryCoproductIso E).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← intervalBoundaryCoproductIso_inclusion hcof hw E, Iso.inv_hom_id_assoc]
  · simp [(circleTensorPoint_isZero E).eq_of_tgt (intervalBoundaryCollapse E) 0]
  · simp
  · simp [(circleTensorPoint_isZero E).eq_of_src (circleTensorBasepoint E) 0]

end SerrePositivity.GeneralSymmetricSpectrum
