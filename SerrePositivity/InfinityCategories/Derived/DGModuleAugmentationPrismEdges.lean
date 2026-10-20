module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationPrismBoundary
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {n : ℕ} (s : Simplex R (DGModuleFunctorResolutionObject R C E F) n)
/-- 任意の実二点部分集合で、混合 prism 係数は閉じている。 -/
lemma dgModuleAugmentationPrismMixedHom_closed_two (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : I.card = 2) :
    differential R (dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData β
      I a b k hI ha hb hk) = 0 := by
  have hk0 : k = 0 := by omega
  subst hk0
  have hs : differential R (s.hom I a b 0 hI ha hb hk) = 0 := by
    rw [s.equation, SimplexData.rhs_of_card_two _ _ _ _ _ _ _ _ _ hc]
  have hm : differential R
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f 0
        (s.hom I a b 0 hI ha hb hk)) = 0 := by
    rw [← map_differential, hs, map_zero]
  have ht : differential R (x := (s.obj b).replacement.val)
      (y := F.obj (s.obj b).source) (dgModuleAugmentationComponent R C E F (s.obj b)).val = 0 :=
    (dgModuleAugmentationComponent R C E F (s.obj b)).property
  rw [dgModuleAugmentationPrismMixedHom_two R C E F s.toSimplexData β I a b 0 hI ha hb hk hc]
  have hgen {A B T : RightModule R E} (g : GradedHom R B T 0) (f : GradedHom R A B 0)
      (hg : differential R g = 0) (hf : differential R f = 0) :
      differential R (compose R g f (add_zero 0)) = 0 := by
    rw [differential_compose, hg, hf]
    simp only [zero_compose, compose_zero, smul_zero, add_zero]
  exact hgen _ _ ht hm
end SerrePositivity.InfinityCategories
