module
public import SerrePositivity.HomologicalAlgebra.LeftDerivedZeroFunctorNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive

/-! # Two-variable naturality of the actual tensor H0 and standard augmentation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The established H0 comparison is also natural in the unresolved factor. -/
lemma realizedDerivedTensorH0NatIso_naturality_left
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        ((realizedDerivedTensorMapLeft R f).app N) ≫
      (realizedDerivedTensorH0NatIso R M').hom.app N =
    (realizedDerivedTensorH0NatIso R M).hom.app N ≫
      ((tensoringLeft (ModuleCat.{u} R)).map f).app N := by
  let α := (tensoringLeft (ModuleCat.{u} R)).map f
  have hn := (chainDerivedRealizationHomologyIso R 0).hom.naturality
    ((NatTrans.leftDerivedToHomotopyCategory α).app N)
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      ((chainDerivedRealization R).map ((NatTrans.leftDerivedToHomotopyCategory α).app N)) ≫
      (chainDerivedRealizationHomologyIso R 0).hom.app _ ≫
      (tensorLeft M').fromLeftDerivedZero.app N =
    (chainDerivedRealizationHomologyIso R 0).hom.app _ ≫
      (tensorLeft M).fromLeftDerivedZero.app N ≫ α.app N
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc]
  exact congrArg ((chainDerivedRealizationHomologyIso R 0).hom.app _ ≫ ·)
    (fromLeftDerivedZero_functor_naturality α N)

/-- H0 of the actual two-sided tensor is natural in its first module. -/
lemma boundedAboveDerivedTensorModuleH0NatIso_naturality_left
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        ((boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map f)
          (𝟙 (boundedAboveDerivedSingleFunctor.obj N)))).hom) ≫
      (boundedAboveDerivedTensorModuleH0NatIso M').hom.app N =
    (boundedAboveDerivedTensorModuleH0NatIso M).hom.app N ≫
      ((tensoringLeft (ModuleCat.{u} R)).map f).app N := by
  have hn := boundedAboveDerivedTensorModuleIso_naturality_left f N
  have hh := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map hn
  simp only [CategoryTheory.Functor.map_comp] at hh
  dsimp only [boundedAboveDerivedTensorModuleH0NatIso, boundedAboveDerivedTensorModuleNatIso]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Category.assoc]
  rw [← Category.assoc, hh, Category.assoc,
    realizedDerivedTensorH0NatIso_naturality_left]

/-- The standard augmentation is natural in the left module, without a flatness hypothesis. -/
lemma boundedAboveDerivedTensorModuleAugmentation_naturality_left
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedSingleFunctor.map f)
        (𝟙 (boundedAboveDerivedSingleFunctor.obj N)))).hom ≫
      (boundedAboveDerivedTensorModuleAugmentation M').app N =
    (boundedAboveDerivedTensorModuleAugmentation M).app N ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (((tensoringLeft (ModuleCat.{u} R)).map f).app N) := by
  apply (derivedNonpositiveHomologyZero_map_bijective
    (X := (boundedAboveDerivedTensorModuleFunctor M).obj N)
    (Y := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      ((tensorLeft M').obj N))).injective
  dsimp only
  apply (cancel_mono ((realizedSingleH0Iso R).hom.app ((tensorLeft M').obj N))).mp
  have hn := (realizedSingleH0Iso R).hom.naturality
    (((tensoringLeft (ModuleCat.{u} R)).map f).app N)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [boundedAboveDerivedTensorModuleAugmentation_homology, hn,
    ← Category.assoc, boundedAboveDerivedTensorModuleAugmentation_homology,
    boundedAboveDerivedTensorModuleH0NatIso_naturality_left]

/-- The actual standard tensor augmentation is natural in both modules at once. -/
lemma boundedAboveDerivedTensorModuleAugmentation_naturality
    {M M' N N' : ModuleCat.{u} R} (f : M ⟶ M') (g : N ⟶ N') :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedSingleFunctor.map f)
        (boundedAboveDerivedSingleFunctor.map g))).hom ≫
      (boundedAboveDerivedTensorModuleAugmentation M').app N' =
    (boundedAboveDerivedTensorModuleAugmentation M).app N ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (f ⊗ₘ g) := by
  have hr := (boundedAboveDerivedTensorModuleAugmentation M').naturality g
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M'))
      (boundedAboveDerivedSingleFunctor.map g))).hom ≫
    (boundedAboveDerivedTensorModuleAugmentation M').app N' =
    (boundedAboveDerivedTensorModuleAugmentation M').app N ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        ((tensorLeft M').map g) at hr
  have ht := (boundedAboveDerivedTensor (R := R)).map_comp
    (CategoryTheory.Prod.mkHom (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj N)))
    (CategoryTheory.Prod.mkHom (𝟙 (boundedAboveDerivedSingleFunctor.obj M'))
      (boundedAboveDerivedSingleFunctor.map g))
  simp only [CategoryTheory.prod_comp, Category.comp_id, Category.id_comp] at ht
  have ht' := congrArg (fun h => h.hom) ht
  change (boundedAboveDerivedTensor.map _).hom =
    (boundedAboveDerivedTensor.map _).hom ≫ (boundedAboveDerivedTensor.map _).hom at ht'
  rw [ht', Category.assoc, hr, ← Category.assoc,
    boundedAboveDerivedTensorModuleAugmentation_naturality_left, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  congr 1
  exact congrArg (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
    (tensorHom_def f g).symm

end SerrePositivity
