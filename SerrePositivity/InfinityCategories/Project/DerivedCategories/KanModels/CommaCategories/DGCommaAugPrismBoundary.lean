module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugPrismData
/-!
概要：実 augmentation prism の候補データの両端と、実辺係数を厳密に回収する。
方針：定値相を評価し、二点集合には内部切断が無いことを使う。
規約：全高次の HA 方程式は別途検証。使われ方：prism の境界固定構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
/-- 定値相零の実データは、同じ実比較対象射影の像。 -/
lemma dgCommaAugmentationPrismData_zero :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s (OrderHom.const _ (0 : Fin 2)) =
      s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext rfl
  rfl
/-- 定値相一の実データは、同じ実入力像の dg 関手の像。 -/
lemma dgCommaAugmentationPrismData_one :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s (OrderHom.const _ (1 : Fin 2)) =
      s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R C E F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext rfl
  rfl
/-- 二点係数には内部切断の補正が無く、元の同じ augmentation と実辺の合成。 -/
lemma dgCommaAugmentationPrismMixedHom_two (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : I.card = 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk =
      _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := (s.obj b).replacement)
        (z := F.obj (s.obj b).source) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R C E F (s.obj b)).val
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
          (s.hom I a b k hI ha hb hk)) (add_zero k) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with h
  · have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
      rw [ha]; exact I.isLeast_min' _
    have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
      rw [hb]; exact I.isGreatest_max' _
    have hp : I = {a, b} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair hc hamin hbmax
    have hm : j.val = a ∨ j.val = b := by simpa [hp] using j.property
    rcases hm with hm | hm <;> omega
  · rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
