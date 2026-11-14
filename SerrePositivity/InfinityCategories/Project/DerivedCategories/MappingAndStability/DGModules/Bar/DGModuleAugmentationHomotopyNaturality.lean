module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationPrismData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStrictNatTrans
/-!
概要：同じ実比較差を通常順の augmentation 合成へ移し、閉辺の自然性ホモトピーを得る。
方針：全 Hom の前後合成の実成分公式と、同じ比較 cochain の微分式を使う。
規約：選び直したホモトピーを導入しない。使われ方：混合三角形の HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
/-- 全整数次数で、実比較差は通常順の同じ augmentation 合成の差。 -/
lemma dgModuleAugmentationBoundary_apply (n : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F X Y).f n a =
      _root_.SerrePositivity.DifferentialGraded.compose R (x := X.replacement.val) (y := F.obj X.source) (z := F.obj Y.source)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F X Y).f n a)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F X).val (zero_add n) -
      _root_.SerrePositivity.DifferentialGraded.compose R (x := X.replacement.val) (y := Y.replacement.val) (z := F.obj Y.source)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F Y).val
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y).f n a) (add_zero n) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomPrecompose_apply R E X.augmentation
    (z := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F X Y).f n a)
  have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomPostcompose_apply R E Y.augmentation
    (z := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y).f n a)
  change (_root_.SerrePositivity.DifferentialGraded.moduleHomPrecompose R E X.replacement.val (F.obj X.source) (F.obj Y.source)
      X.augmentation).f n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F X Y).f n a) -
    (_root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val Y.replacement.val (F.obj Y.source)
      Y.augmentation).f n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y).f n a) = _
  exact congrArg₂ (fun x y ↦ x - y) hp hq
/-- 閉次数零の同じ実射に対し、augmentation の自然性を比較する同じ実ホモトピー。 -/
lemma dgModuleAugmentationHomotopyComponent_closed_zero
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y 0) (ha : _root_.SerrePositivity.DifferentialGraded.differential R a = 0) :
    _root_.SerrePositivity.DifferentialGraded.differential R (x := X.replacement.val) (y := F.obj Y.source)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F X Y 0 a) =
      _root_.SerrePositivity.DifferentialGraded.compose R (x := X.replacement.val) (y := Y.replacement.val) (z := F.obj Y.source)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F Y).val
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y).f 0 a) (by omega) -
      _root_.SerrePositivity.DifferentialGraded.compose R (x := X.replacement.val) (y := F.obj X.source) (z := F.obj Y.source)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F X Y).f 0 a)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F X).val (by omega) := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMinusOneCochain_boundary_closed_zero
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive_boundary R C E F X Y) a ha
  have hb := congrArg Neg.neg (dgModuleAugmentationBoundary_apply R C E F X Y 0 a)
  exact he.trans (hb.trans (neg_sub _ _))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
