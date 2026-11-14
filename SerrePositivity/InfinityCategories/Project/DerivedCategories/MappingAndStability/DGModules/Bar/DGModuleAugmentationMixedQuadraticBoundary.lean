module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationMixedCuts
/-!
概要：実混合候補の二次境界を、同じ基底・比較差・左右補正へ移す。
方針：相別係数の回収と Hom の線形移送、既証明の実微分式を使う。
規約：単体作用の自然性は別工程。使われ方：全 augmentation prism の単体構成。
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
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 実切断係数を内部点の二相で、同じ基底・比較差・左右補正へ分ける。 -/
lemma dgModuleAugmentationMixedTransport_cut
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1)
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).cutCompose I a b k j) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.cutCompose I a b k j) +
      (if β j = 1 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutComparisonBoundary R C E F s I a b k j +
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationImageCorrection R C E F s β I a b k j else
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSuffixCorrection R C E F s β I a b k j) := by
  by_cases hpj : β j = 1
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationMixedTransport_cut_one R C E F s β I a b k
      hI ha hb hk hpa hpb j hj haj hjb hpj, ite_eq_left hpj,
      ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationBaseCut_comparison R C E F s I a b k hk j hj, add_assoc]
  · have hv : (β j).val ≠ 1 := by
      intro he
      exact hpj (Fin.ext he)
    have hp0 : β j = 0 := by
      apply Fin.ext
      have := (β j).isLt
      change (β j).val = 0
      omega
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationMixedTransport_cut_zero R C E F s β I a b k
      hI ha hb hk hpa hpb j hj haj hjb hp0, ite_eq_right hpj]
/-- 実混合候補の全二次境界は、基底二次境界・比較差・同じ左右補正の合成和。 -/
lemma dgModuleAugmentationMixedTransport_quadraticBoundary
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).quadraticBoundary I a b k) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.quadraticBoundary I a b k) +
      (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutComparisonBoundary R C E F s I a b k j) +
      (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationImageCorrection R C E F s β I a b k j) +
      (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSuffixCorrection R C E F s β I a b k j) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.quadraticBoundary, Units.smul_def, map_sum, map_zsmul,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints_eq_filter_interior, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  rw [dgModuleAugmentationMixedTransport_cut R C E F s β I a b k hI ha hb hk
    hpa hpb j hm.1 hm.2.1 hm.2.2]
  by_cases hpj : β j = 1 <;> simp [hpj, smul_add, add_assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
