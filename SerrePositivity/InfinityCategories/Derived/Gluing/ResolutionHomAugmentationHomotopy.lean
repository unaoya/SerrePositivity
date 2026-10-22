module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedCochainHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionComparison

/-! 分解の同じ全比較 cochain は、二つの実 Hom 作用の全空間ホモトピーを与える。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R C (RightModule R E)) (X Y : DGModuleFunctorResolutionObject R C E F)

def dgGluingResolutionHomInputAugmentation :
    dgModuleFunctorResolutionHomComplex R C E F X Y ⟶
      moduleHom R E X.replacement.val (F.obj Y.source) :=
  dgModuleFunctorResolutionImageHomMap R C E F X Y ≫
    eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (F.obj Y.source))

def dgGluingResolutionHomOutputAugmentation :
    dgModuleFunctorResolutionHomComplex R C E F X Y ⟶
      moduleHom R E X.replacement.val (F.obj Y.source) :=
  dgModuleFunctorResolutionReplacementHomMap R C E F X Y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement.val)
      Y.augmentation

lemma dgGluingResolutionHomAugmentation_boundary :
    δ (-1) 0 (dgModuleFunctorResolutionPrimitive R C E F X Y) =
      Cochain.ofHom (dgGluingResolutionHomOutputAugmentation R C E F X Y -
        dgGluingResolutionHomInputAugmentation R C E F X Y) := by
  have hb := dgModuleFunctorResolutionPrimitive_boundary R C E F X Y
  change δ (-1) 0 (dgModuleFunctorResolutionPrimitive R C E F X Y) +
    Cochain.ofHom (dgGluingResolutionHomInputAugmentation R C E F X Y -
      dgGluingResolutionHomOutputAugmentation R C E F X Y) = 0 at hb
  simpa only [Cochain.ofHom_sub, neg_sub] using eq_neg_of_add_eq_zero_left hb

def dgGluingResolutionHomAugmentationHomotopy :
    SSet.Homotopy
      (complexPinchedMap.{u, r} (dgGluingResolutionHomInputAugmentation R C E F X Y))
      (complexPinchedMap.{u, r} (dgGluingResolutionHomOutputAugmentation R C E F X Y)) :=
  dgGluingComplexPinchedHomotopy_of_cochain _ _
    (dgModuleFunctorResolutionPrimitive R C E F X Y)
    (dgGluingResolutionHomAugmentation_boundary R C E F X Y)

end SerrePositivity.InfinityCategories
