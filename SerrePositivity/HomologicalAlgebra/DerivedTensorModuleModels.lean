module
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor

/-! # Compute the actual derived tensor of modules with one unresolved factor -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Removing a module resolution on one side preserves quasi-isomorphisms when the
other side is a bounded-above projective complex. No flatness of the module is needed. -/
lemma moduleResolutionTensorAugmentation_quasiIso (M : ModuleCat.{u} R)
    {X : DerivedCategory (ModuleCat.{u} R)} (P : BoundedAboveDerivedModel X) :
    QuasiIso (cochainTensorMap (projectiveResolutionCochainAugmentation
      (projectiveResolution M)) (𝟙 P.complex)) := by
  apply cochainTensor_quasiIso_left_of_boundedAboveFlat P.complex P.bound 0 0
  · exact fun i hi => P.complex.isZero_of_isStrictlyLE P.bound i hi
  · exact extRes_isZero_X (projectiveResolution M)
  · exact fun i hi => CochainComplex.isZero_of_isStrictlyLE
      ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M) 0 i hi
  · intro i
    have : Module.Projective R (P.complex.X i) := inferInstance
    infer_instance

/-- The actual tensor of two degree-zero modules is computed by resolving only the second. -/
def derivedTensorModuleModelIso (M N : ModuleCat.{u} R) :
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)).obj ≅
      DerivedCategory.Q.obj (cochainTensor (cochainSingleZero M)
        (extRes (projectiveResolution N))) := by
  let P := projectiveResolutionDerivedModel (projectiveResolution M)
  let Q := projectiveResolutionDerivedModel (projectiveResolution N)
  have := moduleResolutionTensorAugmentation_quasiIso M Q
  exact boundedAboveDerivedTensorModelIso _ _ P Q ≪≫
    asIso (DerivedCategory.Q.map (cochainTensorMap
      (projectiveResolutionCochainAugmentation (projectiveResolution M)) (𝟙 Q.complex)))

/-- The one-sided computation respects module maps in both factors. -/
lemma derivedTensorModuleModelIso_naturality {M M' N N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f) (boundedAboveDerivedSingleFunctor.map g))).hom ≫
        (derivedTensorModuleModelIso M' N').hom =
      (derivedTensorModuleModelIso M N).hom ≫ DerivedCategory.Q.map (cochainTensorMap
        ((CochainComplex.singleFunctor (ModuleCat R) 0).map f)
        (extLift (projectiveResolution N) g (projectiveResolution N'))) := by
  let P := projectiveResolution M
  let P' := projectiveResolution M'
  let Q := projectiveResolution N
  let Q' := projectiveResolution N'
  have represent {A B : ModuleCat.{u} R} (h : A ⟶ B) :
      DerivedCategory.Q.map (extLift (projectiveResolution A) h (projectiveResolution B)) ≫
          (projectiveResolutionDerivedModel (projectiveResolution B)).iso.hom =
        (projectiveResolutionDerivedModel (projectiveResolution A)).iso.hom ≫
          (boundedAboveDerivedSingleFunctor.map h).hom := by
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      projectiveResolutionCochainAugmentation_naturality]
  have hn := boundedAboveDerivedTensorModelIso_naturality
    (projectiveResolutionDerivedModel P) (projectiveResolutionDerivedModel P')
    (projectiveResolutionDerivedModel Q) (projectiveResolutionDerivedModel Q')
    (boundedAboveDerivedSingleFunctor.map f) (boundedAboveDerivedSingleFunctor.map g)
    (extLift P f P') (extLift Q g Q') (represent f) (represent g)
  simp only [derivedTensorModuleModelIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    cochainTensorMap_comp, cochainTensorMap_comp]
  simp only [Category.id_comp]
  rw [projectiveResolutionCochainAugmentation_naturality]
  dsimp only [P, P', Q, Q', projectiveResolutionDerivedModel]
  rw [Category.comp_id]

end SerrePositivity
