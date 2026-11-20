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

/-- The free-zero comparison is natural in the tensor parameter. -/
@[reassoc] lemma tensorFreeZeroPointwiseIso_post {X Y : C} (f : X ⟶ Y)
    (E : GeneralSymmetricSpectrum C K) :
    ((freeAt (K := K) 0).map f ▷ E) ≫ (tensorFreeZeroPointwiseIso Y E).hom =
      (tensorFreeZeroPointwiseIso X E).hom ≫ pointwiseTensorPost f E := by
  exact congrArg (fun k => k.app E) (tensorFreeZeroPointwiseBifunctorIso.hom.naturality f)

lemma pointwiseTensorAssociator_inv_level (X Y : C) (E : GeneralSymmetricSpectrum C K)
    (n : ℕ) : (pointwiseTensorAssociator X Y E).inv.hom.app (FiniteBijection.of n) =
      (α_ X Y (level E n)).inv :=
  SymmetricSequence.pointwiseTensorModuleAssociator_inv_level
    (SymmetricSequence.tensorPowerSequence K) X Y E n

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

lemma pointwiseTensorUnitIso_level (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    (pointwiseTensorUnitIso E).hom.hom.app (FiniteBijection.of n) =
      (λ_ (level E n)).hom :=
  SymmetricSequence.pointwiseTensorModuleUnit_levelLaw
    (SymmetricSequence.tensorPowerSequence K) E n

abbrev pointwiseTensorPentagonLaw (X Y Z : C) (E : GeneralSymmetricSpectrum C K) : Prop :=
  SymmetricSequence.pointwiseActionPentagonLaw (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorPost X Y Z E

lemma pointwiseTensor_pentagon (X Y Z : C) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorPentagonLaw X Y Z E :=
  SymmetricSequence.pointwiseAction_pentagon (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorPost pointwiseTensorAssociator_level
    pointwiseTensorPost_level X Y Z E

/-- The action pentagon expressed using the bifunctor and its natural associator. -/
lemma pointwiseTensorBifunctor_pentagon (X Y Z : C) (E : GeneralSymmetricSpectrum C K) :
    (pointwiseTensorBifunctor.map (α_ X Y Z).hom).app E ≫
      (pointwiseTensorAssociatorNatIso X (Y ⊗ Z)).hom.app E ≫
        (pointwiseTensorBifunctor.obj X).map ((pointwiseTensorAssociatorNatIso Y Z).hom.app E) =
    (pointwiseTensorAssociatorNatIso (X ⊗ Y) Z).hom.app E ≫
      (pointwiseTensorAssociatorNatIso X Y).hom.app ((pointwiseTensorBifunctor.obj Z).obj E) :=
  pointwiseTensor_pentagon X Y Z E

abbrev pointwiseTensorTriangleLaw (X : C) (E : GeneralSymmetricSpectrum C K) : Prop :=
  SymmetricSequence.pointwiseActionTriangleLaw (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorUnitIso pointwiseTensorPost X E

lemma pointwiseTensor_triangle (X : C) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorTriangleLaw X E :=
  SymmetricSequence.pointwiseAction_triangle (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorUnitIso pointwiseTensorPost
    pointwiseTensorAssociator_level pointwiseTensorUnitIso_level pointwiseTensorPost_level X E

abbrev pointwiseTensorLeftUnitLaw (X : C) (E : GeneralSymmetricSpectrum C K) : Prop :=
  SymmetricSequence.pointwiseActionLeftUnitLaw (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorUnitIso pointwiseTensorPost X E

lemma pointwiseTensor_left_unit (X : C) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorLeftUnitLaw X E :=
  SymmetricSequence.pointwiseAction_left_unit (SymmetricSequence.tensorPowerSequence K)
    pointwiseTensorAssociator pointwiseTensorUnitIso pointwiseTensorPost
    pointwiseTensorAssociator_level pointwiseTensorUnitIso_level pointwiseTensorPost_level X E

/-- The action triangle expressed using the bifunctor and its unit and associator. -/
lemma pointwiseTensorBifunctor_triangle (X : C) (E : GeneralSymmetricSpectrum C K) :
    (pointwiseTensorAssociatorNatIso X (𝟙_ C)).hom.app E ≫
      (pointwiseTensorBifunctor.obj X).map (pointwiseTensorUnitNatIso.hom.app E) =
        (pointwiseTensorBifunctor.map (ρ_ X).hom).app E :=
  pointwiseTensor_triangle X E

/-- The left unit law expressed using the bifunctor and its unit and associator. -/
lemma pointwiseTensorBifunctor_left_unit (X : C) (E : GeneralSymmetricSpectrum C K) :
    (pointwiseTensorAssociatorNatIso (𝟙_ C) X).hom.app E ≫
      pointwiseTensorUnitNatIso.hom.app ((pointwiseTensorBifunctor.obj X).obj E) =
        (pointwiseTensorBifunctor.map (λ_ X).hom).app E :=
  pointwiseTensor_left_unit X E

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
