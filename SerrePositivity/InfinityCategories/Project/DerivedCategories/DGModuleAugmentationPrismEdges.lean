module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationPrismBoundary
/-!
概要：実 augmentation prism の混合辺係数は、元の同じ閉零辺から閉零射を与える。
方針：二点の実切断和が零となる式と、実 dg 関手・閉 augmentation の微分式を使う。
規約：任意次元の任意の二点部分集合。使われ方：prism の HA 二点方程式。
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
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 任意の実二点部分集合で、混合 prism 係数は閉じている。 -/
lemma dgModuleAugmentationPrismMixedHom_closed_two (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : I.card = 2) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData β
      I a b k hI ha hb hk) = 0 := by
  have hk0 : k = 0 := by omega
  subst hk0
  have hs : _root_.SerrePositivity.DifferentialGraded.differential R (s.hom I a b 0 hI ha hb hk) = 0 := by
    rw [s.equation, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_of_card_two _ _ _ _ _ _ _ _ _ hc]
  have hm : _root_.SerrePositivity.DifferentialGraded.differential R
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f 0
        (s.hom I a b 0 hI ha hb hk)) = 0 := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential, hs, map_zero]
  have ht : _root_.SerrePositivity.DifferentialGraded.differential R (x := (s.obj b).replacement.val)
      (y := F.obj (s.obj b).source) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj b)).val = 0 :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj b)).property
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom_two R C E F s.toSimplexData β I a b 0 hI ha hb hk hc]
  have hgen {A B T : _root_.SerrePositivity.DifferentialGraded.RightModule R E} (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R B T 0) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R A B 0)
      (hg : _root_.SerrePositivity.DifferentialGraded.differential R g = 0) (hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0) :
      _root_.SerrePositivity.DifferentialGraded.differential R (_root_.SerrePositivity.DifferentialGraded.compose R g f (add_zero 0)) = 0 := by
    rw [_root_.SerrePositivity.DifferentialGraded.differential_compose, hg, hf]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
  exact hgen _ _ ht hm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
