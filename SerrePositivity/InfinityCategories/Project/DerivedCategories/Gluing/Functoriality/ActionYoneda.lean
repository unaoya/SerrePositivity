module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Augmentations.AugmentationElements
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.RepresentableModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ActionElements

/-! 元の双加群作用と代表加群表示の前後合成の全 Hom 鎖写像の一致。 -/
@[expose] public section
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
lemma dgGluingRightAction_yoneda (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    M.toFunctor.map X.right Y.right ≫
      eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)
        (ForgetEnrichment.of (Complex R) (M.rightAt Y.right)) ≫
      (dgYonedaIso R X.left (M.rightAt Y.right)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change (dgYonedaIso R X.left (M.rightAt Y.right)).hom.f n
    ((eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)
      (ForgetEnrichment.of (Complex R) (M.rightAt Y.right))).f n
        ((M.toFunctor.map X.right Y.right).f n g)) = _
  dsimp only [dgYonedaIso]
  rw [yonedaEvaluateFamily_apply]
  erw [moduleHomWhiskerRight_apply_π R C
    (P := ForgetEnrichment.of (Complex R) (M.rightAt Y.right))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)
    n ((M.toFunctor.map X.right Y.right).f n g) X.left]
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  change (((moduleHomπ R C (M.rightAt X.right) (M.rightAt Y.right) X.left).f n
    ((M.toFunctor.map X.right Y.right).f n g)).v 0 n (zero_add n))
    (((moduleEvaluation R C X.left).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)).f 0
      (unitElement R X.left).val) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation_unit, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction_apply]
  rfl


lemma dgGluingLeftAction_yoneda (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    yonedaHom R C X.left Y.left ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R X.left))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y) ≫
      (dgYonedaIso R X.left (M.rightAt Y.right)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (dgYonedaIso R X.left (M.rightAt Y.right)).hom.f n
    ((eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R X.left))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y)).f n ((yonedaHom R C X.left Y.left).f n f)) = _
  dsimp only [dgYonedaIso]
  rw [yonedaEvaluateFamily_apply]
  change (((eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (representable R X.left))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y) ≫
    moduleHomπ R C (representable R X.left) (M.rightAt Y.right) X.left).f n
      ((yonedaHom R C X.left Y.left).f n f)).v 0 n (zero_add n))
        (unitElement R X.left).val = _
  erw [moduleHomWhiskerLeft_π R C
    (M := ForgetEnrichment.of (Complex R) (representable R X.left))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y) X.left]
  change (((moduleHomπ R C (representable R X.left) (representable R Y.left) X.left).f n
    ((yonedaHom R C X.left Y.left).f n f)).comp
      (Cochain.ofHom ((moduleEvaluation R C X.left).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y))) (add_zero n)).v 0 n (zero_add n)
        (unitElement R X.left).val = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  change ((moduleEvaluation R C X.left).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y)).f n
    ((((moduleHomπ R C (representable R X.left) (representable R Y.left) X.left).f n
      ((yonedaHom R C X.left Y.left).f n f)).v 0 n (zero_add n))
        (unitElement R X.left).val) = _
  rw [yonedaHom_element]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction_apply]
  rw [forward_unit]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
