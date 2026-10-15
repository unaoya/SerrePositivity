module
public import SerrePositivity.HomologicalAlgebra.DerivedNonpositiveHom
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison

/-! # Upper bounds and the universal property of the actual derived tensor of modules -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- A projective derived model can retain any specified cohomological upper bound. -/
lemma exists_boundedAboveDerivedModel_at_bound
    (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) [X.IsLE n] :
    ∃ P : BoundedAboveDerivedModel X, P.bound = n := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X n
  obtain ⟨P, ε, hε, hP, hb⟩ := exists_boundedAbove_projective_resolution K n
  let model : BoundedAboveDerivedModel X :=
    ⟨P, n, hb, hP, asIso (DerivedCategory.Q.map ε) ≪≫ e.symm⟩
  exact ⟨model, rfl⟩

/-- The actual derived tensor adds cohomological upper bounds, without flatness. -/
lemma boundedAboveDerivedTensor_isLE_add
    (X Y : DerivedCategory.Minus (ModuleCat.{u} R)) (m n : ℤ)
    [X.obj.IsLE m] [Y.obj.IsLE n] :
    (boundedAboveDerivedTensor.obj (X, Y)).obj.IsLE (m + n) := by
  obtain ⟨P, hP⟩ := exists_boundedAboveDerivedModel_at_bound X.obj m
  obtain ⟨Q, hQ⟩ := exists_boundedAboveDerivedModel_at_bound Y.obj n
  have hb := cochainTensor_isStrictlyLE P.complex Q.complex P.bound Q.bound
  rw [hP, hQ] at hb
  have : (DerivedCategory.Q.obj (cochainTensor P.complex Q.complex)).IsLE (m + n) :=
    inferInstance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (boundedAboveDerivedTensorModelIso X Y P Q).symm (m + n)

/-- Derived tensor preserves nonpositive objects in both variables. -/
instance boundedAboveDerivedTensor_isLE_zero
    (X Y : DerivedCategory.Minus (ModuleCat.{u} R))
    [X.obj.IsLE 0] [Y.obj.IsLE 0] :
    (boundedAboveDerivedTensor.obj (X, Y)).obj.IsLE 0 := by
  simpa only [add_zero] using boundedAboveDerivedTensor_isLE_add X Y 0 0

/-- A map from a nonpositive derived tensor into a discrete module is determined by H0. -/
lemma boundedAboveDerivedTensor_hom_ext
    (X Y : DerivedCategory.Minus (ModuleCat.{u} R))
    [X.obj.IsLE 0] [Y.obj.IsLE 0] (M : ModuleCat.{u} R)
    (f g : (boundedAboveDerivedTensor.obj (X, Y)).obj ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
    (h : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map g) : f = g :=
  (derivedNonpositiveHomologyZero_map_bijective
    (X := (boundedAboveDerivedTensor.obj (X, Y)).obj)
    (Y := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).injective h

/-- The actual tensor of degree-zero modules has no positive cohomology. -/
instance boundedAboveDerivedTensorModule_isLE_zero (M N : ModuleCat.{u} R) :
    ((boundedAboveDerivedTensorModuleFunctor M).obj N).IsLE 0 := by
  change (boundedAboveDerivedTensor.obj
    (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)).obj.IsLE 0
  have : (boundedAboveDerivedSingleFunctor.obj M).obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M).IsLE 0
    infer_instance
  have : (boundedAboveDerivedSingleFunctor.obj N).obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N).IsLE 0
    infer_instance
  exact boundedAboveDerivedTensor_isLE_zero _ _

/-- All maps from the derived tensor of discrete modules to a discrete module
are ordinary maps out of the ordinary tensor, normalized by the established comparisons. -/
def boundedAboveDerivedTensorModuleHomEquiv (M N U : ModuleCat.{u} R) :
    ((boundedAboveDerivedTensorModuleFunctor M).obj N ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj U) ≃
      ((tensorLeft M).obj N ⟶ U) :=
  (Equiv.ofBijective
    (fun f : (boundedAboveDerivedTensorModuleFunctor M).obj N ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj U =>
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f)
    (derivedNonpositiveHomologyZero_map_bijective)).trans
      (Iso.homCongr ((boundedAboveDerivedTensorModuleH0NatIso M).app N)
        ((realizedSingleH0Iso R).app U))

/-- Explicit normalization of the ordinary tensor universal property. -/
@[simp] lemma boundedAboveDerivedTensorModuleHomEquiv_apply
    (M N U : ModuleCat.{u} R)
    (f : (boundedAboveDerivedTensorModuleFunctor M).obj N ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj U) :
    boundedAboveDerivedTensorModuleHomEquiv M N U f =
      ((boundedAboveDerivedTensorModuleH0NatIso M).app N).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f ≫
        (realizedSingleH0Iso R).hom.app U := rfl

/-- The ordinary tensor universal property is natural in the target module. -/
lemma boundedAboveDerivedTensorModuleHomEquiv_postcomp
    (M N : ModuleCat.{u} R) {U V : ModuleCat.{u} R}
    (f : (boundedAboveDerivedTensorModuleFunctor M).obj N ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj U) (g : U ⟶ V) :
    boundedAboveDerivedTensorModuleHomEquiv M N V
        (f ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map g) =
      boundedAboveDerivedTensorModuleHomEquiv M N U f ≫ g := by
  rw [boundedAboveDerivedTensorModuleHomEquiv_apply,
    boundedAboveDerivedTensorModuleHomEquiv_apply, CategoryTheory.Functor.map_comp]
  have hn := (realizedSingleH0Iso R).hom.naturality g
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simpa only [Category.assoc] using congrArg
    (fun k => ((boundedAboveDerivedTensorModuleH0NatIso M).app N).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f ≫ k) hn

/-- The existing augmentation is the unique map corresponding to the identity tensor map. -/
@[simp] lemma boundedAboveDerivedTensorModuleHomEquiv_augmentation
    (M N : ModuleCat.{u} R) :
    boundedAboveDerivedTensorModuleHomEquiv M N ((tensorLeft M).obj N)
      ((boundedAboveDerivedTensorModuleAugmentation M).app N) = 𝟙 _ := by
  change ((boundedAboveDerivedTensorModuleH0NatIso M).app N).inv ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      ((boundedAboveDerivedTensorModuleAugmentation M).app N) ≫
    (realizedSingleH0Iso R).hom.app ((tensorLeft M).obj N) = _
  rw [boundedAboveDerivedTensorModuleAugmentation_homology]
  exact ((boundedAboveDerivedTensorModuleH0NatIso M).app N).inv_hom_id

/-- The inverse universal comparison is the established standard augmentation
followed by the single-object image of the specified ordinary tensor map. -/
lemma boundedAboveDerivedTensorModuleHomEquiv_symm_apply
    (M N U : ModuleCat.{u} R) (f : (tensorLeft M).obj N ⟶ U) :
    (boundedAboveDerivedTensorModuleHomEquiv M N U).symm f =
      (boundedAboveDerivedTensorModuleAugmentation M).app N ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map f := by
  apply (boundedAboveDerivedTensorModuleHomEquiv M N U).injective
  rw [Equiv.apply_symm_apply, boundedAboveDerivedTensorModuleHomEquiv_postcomp,
    boundedAboveDerivedTensorModuleHomEquiv_augmentation, Category.id_comp]

end SerrePositivity
