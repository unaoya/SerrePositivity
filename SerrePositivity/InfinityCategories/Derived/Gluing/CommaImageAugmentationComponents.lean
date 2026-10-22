module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImageFunctor
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismData

/-! 恒等 comma への実 dg 関手は、augmentation prism の二作用と全比較 cochain 成分を保存。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex HomologicalComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : DGFunctorCommaObject R C E F)
local notation "IX" => dgGluingCommaImageObject R C E F X
local notation "IY" => dgGluingCommaImageObject R C E F Y

lemma dgGluingCommaImageAugmentationSource_component (k : ℤ) (a : GradedHom R X Y k) :
    ((dgCommaAugmentationSource R E E (DGFunctor.id E)).map IX IY).f k
        ((dgGluingCommaImageHomMap R C E F X Y).f k a) =
      ((dgCommaAugmentationSource R C E F).map X Y).f k a :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (dgGluingCommaImageHomMap_replacement R C E F X Y) k) a

lemma dgGluingCommaImageAugmentationTarget_component (k : ℤ) (a : GradedHom R X Y k) :
    ((dgCommaAugmentationTarget R E E (DGFunctor.id E)).map IX IY).f k
        ((dgGluingCommaImageHomMap R C E F X Y).f k a) =
      ((dgCommaAugmentationTarget R C E F).map X Y).f k a :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (dgGluingCommaImageHomMap_image R C E F X Y) k) a

lemma dgGluingCommaImageAugmentationHomotopy_component (k : ℤ) (a : GradedHom R X Y k) :
    dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E) IX IY k
        ((dgGluingCommaImageHomMap R C E F X Y).f k a) =
      dgCommaAugmentationHomotopyComponent R C E F X Y k a := by
  have hh := Cochain.congr_v (dgGluingCommaImageHomMap_primitive R C E F X Y)
    k (k - 1) (by omega)
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at hh
  exact ConcreteCategory.congr_hom hh a

omit Y in
lemma dgGluingCommaImageAugmentationComponent :
    (dgCommaAugmentationComponent R E E (DGFunctor.id E) IX).val =
      (dgCommaAugmentationComponent R C E F X).val := rfl

end SerrePositivity.InfinityCategories
