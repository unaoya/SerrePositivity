module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorHomModelMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.ResolutionHomAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionProjections

/-! 実分解圏の元の二つの nerve 射影の Hom 作用を、同じ全比較 cochain で結ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (X Y : DGModuleFunctorResolutionObject R C E F)

def dgGluingResolutionActualHomInput :
    DGNerve.pinchedHom R (DGModuleFunctorResolutionObject R C E F) X Y ⟶
      complexPinchedSpace.{u, max (u + 1) v}
        (moduleHom R E X.replacement.val (F.obj Y.source)) :=
  dgGluingFunctorHomModelMap ((dgModuleFunctorResolutionSource R C E F).comp F) X Y ≫
    complexPinchedMap.{u, max (u + 1) v}
      (eHomWhiskerRight (Complex R) X.augmentation
        (ForgetEnrichment.of (Complex R) (F.obj Y.source)))

def dgGluingResolutionActualHomOutput :
    DGNerve.pinchedHom R (DGModuleFunctorResolutionObject R C E F) X Y ⟶
      complexPinchedSpace.{u, max (u + 1) v}
        (moduleHom R E X.replacement.val (F.obj Y.source)) :=
  dgGluingFunctorHomModelMap (dgModuleFunctorResolutionReplacement R C E F) X Y ≫
    complexPinchedMap.{u, max (u + 1) v}
      (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement.val)
        Y.augmentation)

lemma dgGluingResolutionActualHomInput_eq :
    dgGluingResolutionActualHomInput R C E F X Y =
      (pinchedComplexModelIso X Y).hom ≫ complexPinchedMap.{u, max (u + 1) v}
        (dgGluingResolutionHomInputAugmentation R C E F X Y) := by
  rw [dgGluingResolutionActualHomInput, dgGluingFunctorHomModelMap_eq,
    Category.assoc, ← complexPinchedMap_comp]
  rfl

lemma dgGluingResolutionActualHomOutput_eq :
    dgGluingResolutionActualHomOutput R C E F X Y =
      (pinchedComplexModelIso X Y).hom ≫ complexPinchedMap.{u, max (u + 1) v}
        (dgGluingResolutionHomOutputAugmentation R C E F X Y) := by
  rw [dgGluingResolutionActualHomOutput, dgGluingFunctorHomModelMap_eq,
    Category.assoc, ← complexPinchedMap_comp]
  rfl

def dgGluingResolutionActualHomAugmentationHomotopy :
    SSet.Homotopy (dgGluingResolutionActualHomInput R C E F X Y)
      (dgGluingResolutionActualHomOutput R C E F X Y) := by
  rw [dgGluingResolutionActualHomInput_eq, dgGluingResolutionActualHomOutput_eq]
  exact functorHomotopyPrecomp
    (dgGluingResolutionHomAugmentationHomotopy.{u, max (u + 1) v, v, max (u + 1) v}
      R C E F X Y) (pinchedComplexModelIso X Y).hom

end SerrePositivity.InfinityCategories
