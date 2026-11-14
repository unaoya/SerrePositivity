module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugHomotopyData
/-!
概要：比較 cochain の二つの実 tensor 項を、任意整数次数の斉次射上で評価する。
方針：左右 tensor の実成分公式で、第二項の Koszul 符号を確定する。
規約：符号は第一斉次射の次数に依存。使われ方：augmentation prism の切断係数。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory HomologicalComplex
  CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
  (p q : ℤ) (a : GradedHom R X Y p) (b : GradedHom R Y Z q)
/-- 第一比較項には、右 tensor による追加符号がない。 -/
lemma dgCommaAugmentationHomotopy_firstTensor_apply :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R C E F X Y Z).v
      (p + q) (p + q - 1) (by omega)
      (ιTensorObj (homObject R _ X Y) (homObject R _ Y Z) p q (p + q) rfl (a ⊗ₜ[R] b)) =
    forward R (x := X.replacement) (y := F.obj Y.source) (z := F.obj Z.source)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X Y p a)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z).f q b) (by omega) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.comp_apply]
  have he := tensorRightHom_apply_of_sum
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
    (homObject R E X.replacement (F.obj Y.source))
    (-1) p q (p + q) (p - 1) (p + q - 1) rfl (by omega) (by omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y) a b
  have ht := congrArg ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F X Y Z).f
    (p + q - 1)) he
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap, HomologicalComplex.comp_f,
    ModuleCat.comp_apply, tensorMap_apply, HomologicalComplex.id_f, ModuleCat.id_apply,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent, forward] using! ht
/-- 第二比較項の追加符号は、第一斉次射の次数 p による。 -/
lemma dgCommaAugmentationHomotopy_secondTensor_apply :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F X Y Z).v
      (p + q) (p + q - 1) (by omega)
      (ιTensorObj (homObject R _ X Y) (homObject R _ Y Z) p q (p + q) rfl (a ⊗ₜ[R] b)) =
    p.negOnePow • forward R
      (x := X.replacement) (y := Y.replacement) (z := F.obj Z.source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f p a)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F Y Z q b) (by omega) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.comp_apply]
  have he := tensorLeftHom_apply_of_sum
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
    (homObject R E Y.replacement (F.obj Z.source))
    (-1) p q (p + q) (q - 1) (p + q - 1) rfl (by omega) (by omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z) a b
  have ht := congrArg ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F X Y Z).f
    (p + q - 1)) he
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap, HomologicalComplex.comp_f,
    ModuleCat.comp_apply, Units.smul_def, map_zsmul, tensorMap_apply,
    HomologicalComplex.id_f, ModuleCat.id_apply, neg_one_mul, Int.negOnePow_neg,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent, forward] using! ht
end SerrePositivity.InfinityCategories.Project.DerivedCategories
