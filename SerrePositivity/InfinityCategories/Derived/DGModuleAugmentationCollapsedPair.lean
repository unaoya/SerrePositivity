module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationDegenerateReindex
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {m n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 実候補の潰れた二点係数は、引き戻しの両側で同じ実単位となる。 -/
lemma dgModuleAugmentationPrismData_hom_pullback_of_collapsed_pair
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))))
    (hc : I.card = 2) :
    (dgModuleAugmentationPrismData R C E F (s.pullback α) (β.comp α)).hom
        I a b k hI ha hb hk =
      ((dgModuleAugmentationPrismData R C E F s β).pullback α).hom I a b k hI ha hb hk := by
  have hk0 : k = 0 := by omega
  subst hk0
  have hab : α a = α b := Index.collapse_two hi hc
    (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
  let p : Fin 2 := β (α b)
  have hpa : (β.comp α) a = p := congrArg β hab
  have hpb : (β.comp α) b = p := rfl
  have hl := dgModuleAugmentationPrismData_hom_phase R C E F (s.pullback α) (β.comp α)
    p I a b 0 hI ha hb hk hpa hpb
  have hs := SimplexData.pullback_hom_of_collapsed_pair s α I a b 0 hI ha hb hk hi hc
  have hm := map_unit_of_heq (dgModuleAugmentationPhaseFunctor R C E F p)
    ((s.pullback α).hom I a b 0 hI ha hb hk) (congrArg s.obj hab) hs
  have hr := SimplexData.pullback_hom_of_collapsed_pair
    (dgModuleAugmentationPrismData R C E F s β) α I a b 0 hI ha hb hk hi hc
  have ho := dgModuleAugmentationPrismData_obj_phase R C E F s β p (α b) rfl
  have hu : ∀ (X Y : RightModule R E), X = Y →
      HEq (unitElement R X).val (unitElement R Y).val := by
    intro X Y h
    cases h
    rfl
  exact eq_of_heq ((hl.trans hm).trans (hr.trans (hu _ _ ho)).symm)
end SerrePositivity.InfinityCategories
