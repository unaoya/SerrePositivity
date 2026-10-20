module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationPrismData
public import SerrePositivity.InfinityCategories.Derived.DGModuleStrictNatTrans
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (X Y : DGModuleFunctorResolutionObject R C E F)
/-- 全整数次数で、実比較差は通常順の同じ augmentation 合成の差。 -/
lemma dgModuleAugmentationBoundary_apply (n : ℤ) (a : GradedHom R X Y n) :
    (dgModuleFunctorResolutionBoundary R C E F X Y).f n a =
      compose R (x := X.replacement.val) (y := F.obj X.source) (z := F.obj Y.source)
        ((dgModuleFunctorResolutionImageHomMap R C E F X Y).f n a)
        (dgModuleAugmentationComponent R C E F X).val (zero_add n) -
      compose R (x := X.replacement.val) (y := Y.replacement.val) (z := F.obj Y.source)
        (dgModuleAugmentationComponent R C E F Y).val
        ((dgModuleFunctorResolutionReplacementHomMap R C E F X Y).f n a) (add_zero n) := by
  have hp := dgModuleHomPrecompose_apply R E X.augmentation
    (z := (dgModuleFunctorResolutionImageHomMap R C E F X Y).f n a)
  have hq := dgModuleHomPostcompose_apply R E Y.augmentation
    (z := (dgModuleFunctorResolutionReplacementHomMap R C E F X Y).f n a)
  change (moduleHomPrecompose R E X.replacement.val (F.obj X.source) (F.obj Y.source)
      X.augmentation).f n ((dgModuleFunctorResolutionImageHomMap R C E F X Y).f n a) -
    (moduleHomPostcompose R E X.replacement.val Y.replacement.val (F.obj Y.source)
      Y.augmentation).f n ((dgModuleFunctorResolutionReplacementHomMap R C E F X Y).f n a) = _
  exact congrArg₂ (fun x y ↦ x - y) hp hq
/-- 閉次数零の同じ実射に対し、augmentation の自然性を比較する同じ実ホモトピー。 -/
lemma dgModuleAugmentationHomotopyComponent_closed_zero
    (a : GradedHom R X Y 0) (ha : differential R a = 0) :
    differential R (x := X.replacement.val) (y := F.obj Y.source)
      (dgModuleAugmentationHomotopyComponent R C E F X Y 0 a) =
      compose R (x := X.replacement.val) (y := Y.replacement.val) (z := F.obj Y.source)
        (dgModuleAugmentationComponent R C E F Y).val
        ((dgModuleFunctorResolutionReplacementHomMap R C E F X Y).f 0 a) (by omega) -
      compose R (x := X.replacement.val) (y := F.obj X.source) (z := F.obj Y.source)
        ((dgModuleFunctorResolutionImageHomMap R C E F X Y).f 0 a)
        (dgModuleAugmentationComponent R C E F X).val (by omega) := by
  have he := complexMinusOneCochain_boundary_closed_zero
    (dgModuleFunctorResolutionPrimitive R C E F X Y)
    (dgModuleFunctorResolutionBoundary R C E F X Y)
    (dgModuleFunctorResolutionPrimitive_boundary R C E F X Y) a ha
  have hb := congrArg Neg.neg (dgModuleAugmentationBoundary_apply R C E F X Y 0 a)
  exact he.trans (hb.trans (neg_sub _ _))
end SerrePositivity.InfinityCategories
