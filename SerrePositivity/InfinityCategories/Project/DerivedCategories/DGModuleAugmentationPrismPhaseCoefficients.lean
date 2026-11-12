module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationPrismBoundary
/-!
概要：全候補の実係数から、二つの端点相で選ばれる同じ斉次係数を回収する。
方針：明示的な相選択の定義を評価し、対象の相違は異種等号で保持する。
規約：全 HA 方程式を仮定しない。使われ方：候補の線形・二次境界との直接比較。
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
/-- 両端相零の実候補係数は、同じ半自由出力像の斉次係数。 -/
lemma dgModuleAugmentationPrismData_hom_zero
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 0) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).hom I a b k hI ha hb hk)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  have he : ∀ (p q : Fin 2) (h : p ≤ q), p = 0 → q = 0 →
      HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismPhaseHom R C E F s β I a b k hI ha hb hk p q h)
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
          (s.hom I a b k hI ha hb hk)) := by
    intro p q h hp hq
    subst p
    subst q
    rfl
  exact he (β a) (β b) _ hpa hpb
/-- 両端相一の実候補係数は、同じ元の入力像の斉次係数。 -/
lemma dgModuleAugmentationPrismData_hom_one
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 1) (hpb : β b = 1) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).hom I a b k hI ha hb hk)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  have he : ∀ (p q : Fin 2) (h : p ≤ q), p = 1 → q = 1 →
      HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismPhaseHom R C E F s β I a b k hI ha hb hk p q h)
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).map (s.obj a) (s.obj b)).f k
          (s.hom I a b k hI ha hb hk)) := by
    intro p q h hp hq
    subst p
    subst q
    rfl
  exact he (β a) (β b) _ hpa hpb
/-- 混合端点相の実候補係数は、元の同じ augmentation 切断補正和。 -/
lemma dgModuleAugmentationPrismData_hom_mixed
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).hom I a b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk) := by
  have he : ∀ (p q : Fin 2) (h : p ≤ q), p = 0 → q = 1 →
      HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismPhaseHom R C E F s β I a b k hI ha hb hk p q h)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk) := by
    intro p q h hp hq
    subst p
    subst q
    rfl
  exact he (β a) (β b) _ hpa hpb
/-- 相零の実候補対象は、同じ半自由出力対象。 -/
lemma dgModuleAugmentationPrismData_obj_zero
    (β : Fin (n + 1) →o Fin 2) (a : Fin (n + 1)) (ha : β a = 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).obj a = (s.obj a).replacement.val := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData, ha, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj]
  rfl
/-- 相一の実候補対象は、元の同じ入力像。 -/
lemma dgModuleAugmentationPrismData_obj_one
    (β : Fin (n + 1) →o Fin 2) (a : Fin (n + 1)) (ha : β a = 1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).obj a = F.obj (s.obj a).source := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData, ha, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj]
  rfl
/-- 正しい全域係数の両端相零の場合は、同じ半自由出力像を回収する。 -/
lemma dgModuleAugmentationPrismData_homOrZero_zero
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 0) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).homOrZero I a b k)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β) I a b k
    hI ha hb hk]
  exact dgModuleAugmentationPrismData_hom_zero R C E F s β I a b k hI ha hb hk hpa hpb
/-- 正しい全域係数の両端相一の場合は、同じ入力像を回収する。 -/
lemma dgModuleAugmentationPrismData_homOrZero_one
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 1) (hpb : β b = 1) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).homOrZero I a b k)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β) I a b k
    hI ha hb hk]
  exact dgModuleAugmentationPrismData_hom_one R C E F s β I a b k hI ha hb hk hpa hpb
/-- 正しい全域係数の混合端点相の場合は、同じ実混合係数を回収する。 -/
lemma dgModuleAugmentationPrismData_homOrZero_mixed
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).homOrZero I a b k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β) I a b k
    hI ha hb hk]
  exact dgModuleAugmentationPrismData_hom_mixed R C E F s β I a b k hI ha hb hk hpa hpb
end SerrePositivity.InfinityCategories.Project.DerivedCategories
