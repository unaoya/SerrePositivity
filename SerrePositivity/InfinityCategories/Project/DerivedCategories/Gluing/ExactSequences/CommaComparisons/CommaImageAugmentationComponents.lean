module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.CommaImageFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugPrismData

/-! 恒等 comma への実 dg 関手は、augmentation prism の二作用と全比較 cochain 成分を保存。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex HomologicalComplex
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F Y

lemma dgGluingCommaImageAugmentationSource_component (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y k) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)).map IX IY).f k
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Y).f k a) =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map X Y).f k a :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_replacement R C E F X Y) k) a

lemma dgGluingCommaImageAugmentationTarget_component (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y k) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)).map IX IY).f k
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Y).f k a) =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R C E F).map X Y).f k a :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_image R C E F X Y) k) a

lemma dgGluingCommaImageAugmentationHomotopy_component (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E) IX IY k
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Y).f k a) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X Y k a := by
  have hh := Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_primitive R C E F X Y)
    k (k - 1) (by omega)
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at hh
  exact ConcreteCategory.congr_hom hh a

omit Y in
lemma dgGluingCommaImageAugmentationComponent :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R E E (DGFunctor.id E) IX).val =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R C E F X).val := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
