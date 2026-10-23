module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaCollapsedPrimitive
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedPrismCutPhase

/-! 終端へ潰した部分で相を上げても、実 augmentation prism の混合補正和は変わらない。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)

lemma dgGluingCommaPrismMixedHom_terminal_sup
    {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) (n + 1))
    (β t : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    dgCommaAugmentationPrismMixedHom R C E F (s.pullback (coherentPrismCut t))
        (β ⊔ t) I a b k hI ha hb hk =
      dgCommaAugmentationPrismMixedHom R C E F (s.pullback (coherentPrismCut t))
        β I a b k hI ha hb hk := by
  unfold dgCommaAugmentationPrismMixedHom
  congr 1
  apply Finset.sum_congr rfl
  rintro ⟨j, hj⟩ _
  by_cases ht : t j = 0
  · have hβ : (β ⊔ t) j = β j := by
      change max (β j) (t j) = β j
      rw [ht, max_eq_left (Fin.zero_le _)]
    simp only [hβ]
  · have hz (γ : Fin (n + 1) →o Fin 2) :
        (if h : a < j ∧ j < b ∧ γ j = 1 then
          dgCommaAugmentationPrismCut R C E F (s.pullback (coherentPrismCut t))
            I a b k hI ha hb hk j hj h.1 h.2.1 else 0) = 0 := by
      split_ifs with h
      · exact dgGluingCommaPrismCut_pullback_collapsed R C E F s (coherentPrismCut t)
          I a b k hI ha hb hk j hj h.1 h.2.1
          (dgGluingCoherentPrismCut_terminal t h.2.1.le ht)
      · rfl
    rw [hz, hz]

end SerrePositivity.InfinityCategories
