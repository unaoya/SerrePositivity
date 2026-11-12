module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationCorrectionDifferential
/-!
概要：同じ augmentation による基底後合成を実 Hom chain map とし、元の HA を移す。
方針：実入力射影と実後合成を合成し、chain map の可換性を同じ実係数で評価する。
規約：次数や対象を選び直さない。使われ方：候補の基底微分と線形・二次境界の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 同じ実入力射影の像と augmentation の後合成からなる全 Hom chain map。 -/
def dgModuleAugmentationBaseHomMap (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) :
    _root_.SerrePositivity.DifferentialGraded.homObject R _ X Y ⟶ _root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val (F.obj Y.source) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map X Y ≫
    _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val Y.replacement.val (F.obj Y.source) Y.augmentation
/-- 全整数次数で、同じ基底 chain map の成分は元の実合成。 -/
lemma dgModuleAugmentationBaseHomMap_apply
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) (k : ℤ) (a : GradedHom R X Y k) :
    (dgModuleAugmentationBaseHomMap R C E F X Y).f k a =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := X.replacement.val) (y := Y.replacement.val) (z := F.obj Y.source)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F Y).val
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map X Y).f k a) (add_zero k) := by
  change (_root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val Y.replacement.val
    (F.obj Y.source) Y.augmentation).f k
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map X Y).f k a) = _
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent] using!
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomPostcompose_apply R E Y.augmentation
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map X Y).f k a)
/-- 同じ実基底係数の微分は、元の HA の線形・二次境界の像。 -/
lemma dgModuleAugmentationBase_simplex_differential {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
      (_root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj b).replacement.val)
        (z := F.obj (s.obj b).source) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj b)).val
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
          (s.hom I a b k hI ha hb hk)) (add_zero k)) =
      (dgModuleAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.toSimplexData.linearBoundary I a b k - s.toSimplexData.quadraticBoundary I a b k) := by
  rw [← dgModuleAugmentationBaseHomMap_apply]
  have he := ConcreteCategory.congr_hom
    ((dgModuleAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).comm k (k + 1))
    (s.hom I a b k hI ha hb hk)
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
    ((dgModuleAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f k
      (s.hom I a b k hI ha hb hk)) =
    (dgModuleAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
      ((_root_.SerrePositivity.DifferentialGraded.homObject R _ (s.obj a) (s.obj b)).d k (k + 1)
        (s.hom I a b k hI ha hb hk)) at he
  have hs := s.equation I a b k hI ha hb hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic] at hs
  change (_root_.SerrePositivity.DifferentialGraded.homObject R _ (s.obj a) (s.obj b)).d k (k + 1)
    (s.hom I a b k hI ha hb hk) = _ at hs
  rw [hs] at he
  exact he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
