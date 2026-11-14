module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ResolutionHomAugmentationChainHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionProjection
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! 射影的な実入力を始域とすると、同じ分解の半自由出力 Hom 射影は準同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R C) C
    (DGFunctor.id (RightModule R C)))
  (hX : moduleHomotopicallyProjective R C (ForgetEnrichment.of (Complex R) X.source))
include hX

lemma dgGluingResolutionProjectiveSource_input_quasiIso :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolutionHomInputAugmentation R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y) := by
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap_quasiIso R (RightModule R C) C _ X Y
  let : QuasiIso (eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) Y.source)) :=
    moduleHomotopicallyProjective_precompose_quasiIso R C
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R C X.replacement) hX X.augmentation X.quasiIso
      (ForgetEnrichment.of (Complex R) Y.source)
  change QuasiIso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y ≫ 𝟙 _) ≫
      eHomWhiskerRight (Complex R) X.augmentation (ForgetEnrichment.of (Complex R) Y.source))
  rw [Category.comp_id]
  infer_instance

lemma dgGluingResolutionProjectiveSource_replacement_quasiIso :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y) := by
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolutionHomInputAugmentation R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y) :=
    dgGluingResolutionProjectiveSource_input_quasiIso R C X Y hX
  let : QuasiIso (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement.val) Y.augmentation) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolution_secondHomMap_quasiIso R (RightModule R C) C _ X Y
  exact (quasiIso_iff_comp_right _ _).mp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolutionHomOutputAugmentation_quasiIso R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
