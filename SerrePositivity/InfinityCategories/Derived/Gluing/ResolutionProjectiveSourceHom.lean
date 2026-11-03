module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ResolutionHomAugmentationChainHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionProjection
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! 射影的な実入力を始域とすると、同じ分解の半自由出力 Hom 射影は準同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (X Y : DGModuleFunctorResolutionObject R (RightModule R C) C
    (DGFunctor.id (RightModule R C)))
  (hX : moduleHomotopicallyProjective R C (ForgetEnrichment.of (Complex R) X.source))
include hX

lemma dgGluingResolutionProjectiveSource_input_quasiIso :
    QuasiIso (dgGluingResolutionHomInputAugmentation R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y) := by
  let : QuasiIso (dgModuleFunctorResolutionSourceHomMap R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y) :=
    dgModuleFunctorResolutionSourceHomMap_quasiIso R (RightModule R C) C _ X Y
  let : QuasiIso (eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) Y.source)) :=
    moduleHomotopicallyProjective_precompose_quasiIso R C
      (dgSemifreeModule_isProjective R C X.replacement) hX X.augmentation X.quasiIso
      (ForgetEnrichment.of (Complex R) Y.source)
  change QuasiIso
    ((dgModuleFunctorResolutionSourceHomMap R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y ≫ 𝟙 _) ≫
      eHomWhiskerRight (Complex R) X.augmentation (ForgetEnrichment.of (Complex R) Y.source))
  rw [Category.comp_id]
  infer_instance

lemma dgGluingResolutionProjectiveSource_replacement_quasiIso :
    QuasiIso (dgModuleFunctorResolutionReplacementHomMap R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y) := by
  let : QuasiIso (dgGluingResolutionHomInputAugmentation R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y) :=
    dgGluingResolutionProjectiveSource_input_quasiIso R C X Y hX
  let : QuasiIso (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement.val) Y.augmentation) :=
    dgModuleFunctorResolution_secondHomMap_quasiIso R (RightModule R C) C _ X Y
  exact (quasiIso_iff_comp_right _ _).mp
    (dgGluingResolutionHomOutputAugmentation_quasiIso R (RightModule R C) C
      (DGFunctor.id (RightModule R C)) X Y)

end SerrePositivity.InfinityCategories
