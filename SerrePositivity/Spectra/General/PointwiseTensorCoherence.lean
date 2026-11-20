module

public import SerrePositivity.Spectra.General.PointwiseTensor
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroConvolutionNaturality
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorCoherence

/-! # Parameter maps and coherence of the C action on general spectra -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

abbrev pointwiseTensorPost {X Y : C} (f : X ⟶ Y) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensor X E ⟶ pointwiseTensor Y E := (pointwiseTensorBifunctor.map f).app E

/-- The parameter map is the ordinary tensor map at every level. -/
lemma pointwiseTensorPost_level {X Y : C} (f : X ⟶ Y)
    (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    (pointwiseTensorPost f E).hom.app (FiniteBijection.of n) = f ▷ level E n := by
  let M := SymmetricSequence.tensorPowerSequence K
  let g := (SymmetricSequence.freeAt 0).map f
  have hn := MonoidalBalancedTensor.freeLeft_naturality M g (𝟙 E)
  have hpost : pointwiseTensorPost f E =
      (SymmetricSequence.pointwiseTensorModuleIso M X E).inv ≫
        (MonoidalBalancedTensor.freeLeftIso M ((SymmetricSequence.freeAt 0).obj X) E).inv ≫
          MonoidalBalancedTensor.moduleMap M (MonoidalFreeModule.freeMap M g) (𝟙 E) ≫
            (MonoidalBalancedTensor.freeLeftIso M ((SymmetricSequence.freeAt 0).obj Y) E).hom ≫
              (SymmetricSequence.pointwiseTensorModuleIso M Y E).hom := by
    simp only [pointwiseTensorPost, pointwiseTensorBifunctor, FunctorTransport.transport_map,
      NatTrans.comp_app]
    change ((SymmetricSequence.pointwiseTensorModuleIso M X E).inv ≫
        (MonoidalBalancedTensor.freeLeftIso M ((SymmetricSequence.freeAt 0).obj X) E).inv) ≫
      MonoidalBalancedTensor.moduleMap M (MonoidalFreeModule.freeMap M g) (𝟙 E) ≫
        ((MonoidalBalancedTensor.freeLeftIso M ((SymmetricSequence.freeAt 0).obj Y) E).hom ≫
          (SymmetricSequence.pointwiseTensorModuleIso M Y E).hom) = _
    simp only [Category.assoc]
  rw [hpost]
  have hmap :
      (MonoidalBalancedTensor.freeLeftIso M ((SymmetricSequence.freeAt 0).obj X) E).inv ≫
          MonoidalBalancedTensor.moduleMap M (MonoidalFreeModule.freeMap M g) (𝟙 E) ≫
            (MonoidalBalancedTensor.freeLeftIso M ((SymmetricSequence.freeAt 0).obj Y) E).hom =
        MonoidalBalancedTensor.tensorLeftMap M g (𝟙 E) := by
    rw [hn, Iso.inv_hom_id_assoc]
  have hmid := congrArg (fun i ↦
    (SymmetricSequence.pointwiseTensorModuleIso M X E).inv ≫ i ≫
      (SymmetricSequence.pointwiseTensorModuleIso M Y E).hom) hmap
  simp only [Category.assoc] at hmid
  rw [hmid]
  simp only [Mod.comp_hom', MonoidalBalancedTensor.tensorLeftMap_hom, Mod.id_hom']
  change (SymmetricSequence.freeZeroConvolutionLevelIso X E.X n).inv ≫
      (g ⊗ₘ 𝟙 E.X).app (FiniteBijection.of n) ≫
        (SymmetricSequence.freeZeroConvolutionLevelIso Y E.X n).hom = _
  rw [SymmetricSequence.freeZeroConvolutionLevelIso_inv_naturality_assoc f (𝟙 E.X) n]
  change (f ⊗ₘ 𝟙 (level E n)) ≫
    (SymmetricSequence.freeZeroConvolutionLevelIso Y E.X n).inv ≫
      (SymmetricSequence.freeZeroConvolutionLevelIso Y E.X n).hom = f ▷ level E n
  rw [Iso.inv_hom_id, Category.comp_id]
  exact tensorHom_id f _

abbrev pointwiseTensorUnitIso (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensor (𝟙_ C) E ≅ E := pointwiseTensorUnitNatIso.app E

abbrev pointwiseTensorPentagonLaw (X Y Z : C) (E : GeneralSymmetricSpectrum C K) : Prop :=
  SymmetricSequence.pointwiseActionPentagonLaw (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorPost X Y Z E

abbrev pointwiseTensorTriangleLaw (X : C) (E : GeneralSymmetricSpectrum C K) : Prop :=
  SymmetricSequence.pointwiseActionTriangleLaw (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorUnitIso pointwiseTensorPost X E

lemma pointwiseTensor_triangle (X : C) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorTriangleLaw X E :=
  SymmetricSequence.pointwiseAction_triangle (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorUnitIso pointwiseTensorPost
    pointwiseTensorAssociator_level
    (SymmetricSequence.pointwiseTensorModuleUnit_levelLaw
      (SymmetricSequence.tensorPowerSequence K)) pointwiseTensorPost_level X E

abbrev pointwiseTensorLeftUnitLaw (X : C) (E : GeneralSymmetricSpectrum C K) : Prop :=
  SymmetricSequence.pointwiseActionLeftUnitLaw (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorUnitIso pointwiseTensorPost X E

lemma pointwiseTensor_left_unit (X : C) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorLeftUnitLaw X E :=
  SymmetricSequence.pointwiseAction_left_unit (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorUnitIso pointwiseTensorPost
    pointwiseTensorAssociator_level
    (SymmetricSequence.pointwiseTensorModuleUnit_levelLaw
      (SymmetricSequence.tensorPowerSequence K)) pointwiseTensorPost_level X E

lemma pointwiseTensorAssociator_parameter_naturality {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorPost (f ⊗ₘ g) E ≫ (pointwiseTensorAssociator X' Y' E).hom =
      (pointwiseTensorAssociator X Y E).hom ≫ pointwiseTensorPost f (pointwiseTensor Y E) ≫
        (pointwiseTensorFunctor X').map (pointwiseTensorPost g E) := by
  apply Mod.hom_ext
  apply SymmetricSequence.hom_ext
  intro n
  change _ ≫ _ = _ ≫ _ ≫ _
  rw [pointwiseTensorPost_level, pointwiseTensorAssociator_level,
    pointwiseTensorAssociator_level, pointwiseTensorPost_level,
    SymmetricSequence.pointwiseTensorModuleFunctor_map_app, pointwiseTensorPost_level]
  simpa only [tensorHom_id, tensorHom_def, whiskerLeft_id, Category.comp_id,
    pointwiseTensor_level, Category.assoc] using associator_naturality f g (𝟙 (level E n))
lemma pointwiseTensorAssociator_parameter_left {X X' : C} (f : X ⟶ X')
    (Y : C) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorPost (f ⊗ₘ 𝟙 Y) E ≫ (pointwiseTensorAssociator X' Y E).hom =
      (pointwiseTensorAssociator X Y E).hom ≫ pointwiseTensorPost f (pointwiseTensor Y E) := by
  apply Mod.hom_ext
  apply SymmetricSequence.hom_ext
  intro n
  change _ ≫ _ = _ ≫ _
  rw [pointwiseTensorPost_level, pointwiseTensorAssociator_level,
    pointwiseTensorAssociator_level, pointwiseTensorPost_level]
  simpa only [tensorHom_id, tensorHom_def, whiskerLeft_id, Category.comp_id,
    pointwiseTensor_level, id_whiskerRight, Category.assoc] using
      associator_naturality f (𝟙 Y) (𝟙 (level E n))

lemma pointwiseTensorAssociator_parameter_right (X : C) {Y Y' : C} (g : Y ⟶ Y')
    (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorPost (𝟙 X ⊗ₘ g) E ≫ (pointwiseTensorAssociator X Y' E).hom =
      (pointwiseTensorAssociator X Y E).hom ≫
        (pointwiseTensorFunctor X).map (pointwiseTensorPost g E) := by
  apply Mod.hom_ext
  apply SymmetricSequence.hom_ext
  intro n
  change _ ≫ _ = _ ≫ _
  rw [pointwiseTensorPost_level, pointwiseTensorAssociator_level,
    pointwiseTensorAssociator_level, SymmetricSequence.pointwiseTensorModuleFunctor_map_app,
    pointwiseTensorPost_level]
  simpa only [id_tensorHom, tensorHom_id, tensorHom_def, whiskerLeft_id,
    id_whiskerRight, Category.comp_id, Category.id_comp, Category.assoc] using
      associator_naturality (𝟙 X) g (𝟙 (level E n))

end SerrePositivity.GeneralSymmetricSpectrum
