module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugDegenerateReindex
/-!
概要：潰れた二点係数の両側を、同じ実単位として照合する。
方針：潰れた端点の相の一致と、元の相関手の単位保存を使う。
規約：元の実係数の単位分岐を使う。使われ方：全添字作用の自然性の最後の分岐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
/-- 実候補の潰れた二点係数は、引き戻しの両側で同じ実単位となる。 -/
lemma dgCommaAugmentationPrismData_hom_pullback_of_collapsed_pair
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))))
    (hc : I.card = 2) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F (s.pullback α) (β.comp α)).hom
        I a b k hI ha hb hk =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β).pullback α).hom I a b k hI ha hb hk := by
  have hk0 : k = 0 := by omega
  subst hk0
  have hab : α a = α b := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc
    (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
  let p : Fin 2 := β (α b)
  have hpa : (β.comp α) a = p := congrArg β hab
  have hpb : (β.comp α) b = p := rfl
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_phase R C E F (s.pullback α) (β.comp α)
    p I a b 0 hI ha hb hk hpa hpb
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair s α I a b 0 hI ha hb hk hi hc
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_unit_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPhaseFunctor R C E F p)
    ((s.pullback α).hom I a b 0 hI ha hb hk) (congrArg s.obj hab) hs
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β) α I a b 0 hI ha hb hk hi hc
  have ho := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_phase R C E F s β p (α b) rfl
  have hu : ∀ (X Y : E), X = Y →
      HEq (_root_.SerrePositivity.DifferentialGraded.unitElement R X).val (_root_.SerrePositivity.DifferentialGraded.unitElement R Y).val := by
    intro X Y h
    cases h
    rfl
  exact eq_of_heq ((hl.trans hm).trans (hr.trans (hu _ _ ho)).symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
