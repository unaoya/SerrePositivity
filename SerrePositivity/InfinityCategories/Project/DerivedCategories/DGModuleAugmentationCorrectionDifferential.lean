module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationCutDifferentialExpansion
/-!
概要：実候補補正の全微分から線形二重和を消し、候補の全削除補正へ置き換える。
方針：同じ内部切断微分の三分解を有限和へ移し、実削除和の相殺を適用する。
規約：残る二次切断和・比較差の同定は別工程。
使われ方：実 prism の全 HA 方程式を、同じ二次境界の等式へ還元する。
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
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ候補補正の微分は、全削除補正・二次切断和・比較差の三項へ分解する。 -/
lemma dgModuleAugmentationPrismCorrection_differential
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection R C E F s.toSimplexData β I a b k) =
    (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection R C E F s.toSimplexData β (I.erase j) a b (k + 1)) +
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k l) -
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l) := by
  have hd :
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection R C E F s.toSimplexData β I a b k) =
      ∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
        (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s.toSimplexData I a b k l) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection, Units.smul_def, map_sum, map_zsmul]
  have he :
      (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
        (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s.toSimplexData I a b k l)) =
      ∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
        (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutLinearBoundary R C E F s.toSimplexData I a b k l +
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k l -
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l) := by
    apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_filter.mp hl
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut_differential_expansion R C E F s I a b k
      hI ha hb hk l hl'.1 hl'.2.1 hl'.2.2.1]
  rw [hd, he]
  simp only [smul_sub, smul_add, smul_neg, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection_linear_cancel R C E F s.toSimplexData
    β I a b k hk
  rw [← eq_neg_of_add_eq_zero_left hl]
/-- 実混合候補の微分から削除二重和を消し、同じ二次切断和と比較差だけを残す。 -/
lemma dgModuleAugmentationPrismMixedHom_differential_reduction
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    let base := _root_.SerrePositivity.DifferentialGraded.compose R
      (x := (s.obj a).replacement.val) (y := (s.obj b).replacement.val)
      (z := F.obj (s.obj b).source) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj b)).val
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) (add_zero k)
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData β I a b k hI ha hb hk) =
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1) base +
    (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection R C E F s.toSimplexData β (I.erase j) a b (k + 1)) +
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k l) -
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l) := by
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom_eq_base_add_correction, map_add,
    dgModuleAugmentationPrismCorrection_differential R C E F s β I a b k hI ha hb hk]
  abel
end SerrePositivity.InfinityCategories.Project.DerivedCategories
