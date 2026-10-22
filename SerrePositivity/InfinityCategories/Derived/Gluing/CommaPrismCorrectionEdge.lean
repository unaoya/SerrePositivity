module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPinchedPrismMixedCoefficient

/-! 二頂点係数には内部切断がなく、元 augmentation の辺に補正項はない。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)

lemma dgGluingCommaPrismCorrectionSum_card_two (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : I.card = 2) :
    dgGluingCommaPrismCorrectionSum R C E F s β I a b k hI ha hb hk = 0 := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have he : I = {a, b} := Index.eq_pair hc hamin hbmax
  dsimp only [dgGluingCommaPrismCorrectionSum]
  apply Finset.sum_eq_zero
  rintro ⟨j, hj⟩ _
  split_ifs with h
  · rw [he] at hj
    rcases Finset.mem_insert.mp hj with hj | hj
    · exact False.elim ((ne_of_gt h.1) hj)
    · exact False.elim ((ne_of_lt h.2.1) (Finset.mem_singleton.mp hj))
  · rfl

lemma dgGluingCommaPrismMixedCoefficient_card_two (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : I.card = 2) :
    dgCommaAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk =
      dgGluingCommaPrismMainCoefficient R C E F s I a b k hI ha hb hk := by
  rw [dgGluingCommaPrismMixedCoefficient_eq,
    dgGluingCommaPrismCorrectionSum_card_two R C E F s β I a b k hI ha hb hk hc, add_zero]

end SerrePositivity.InfinityCategories
