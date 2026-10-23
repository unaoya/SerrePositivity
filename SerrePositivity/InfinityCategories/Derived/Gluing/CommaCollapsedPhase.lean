module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaCollapsedPrimitive
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismPhaseCoefficients

/-! 全て同じ頂点へ潰れた部分では、任意相の混合係数は元の主項だけになる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {m n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
  (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (m + 1) →o Fin 2)
  (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
  (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
  (hk : k = 2 - (I.card : ℤ)) (hab : α a = α b)

include hab in
lemma dgGluingCommaPrismMixedHom_collapsed :
    dgCommaAugmentationPrismMixedHom R C E F (s.pullback α) β I a b k hI ha hb hk =
      compose R (dgCommaAugmentationComponent R C E F (s.obj (α b))).val
        (((dgCommaAugmentationSource R C E F).map (s.obj (α a)) (s.obj (α b))).f k
          ((s.pullback α).hom I a b k hI ha hb hk)) (add_zero k) := by
  unfold dgCommaAugmentationPrismMixedHom
  let z := compose R (dgCommaAugmentationComponent R C E F (s.obj (α b))).val
    (((dgCommaAugmentationSource R C E F).map (s.obj (α a)) (s.obj (α b))).f k
      ((s.pullback α).hom I a b k hI ha hb hk)) (add_zero k)
  change z + _ = z
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  rintro ⟨j, hj⟩ _
  split_ifs with h
  · have hα : α j = α b := le_antisymm (α.monotone h.2.1.le)
      (hab ▸ α.monotone h.1.le)
    exact dgGluingCommaPrismCut_pullback_collapsed R C E F s α
      I a b k hI ha hb hk j hj h.1 h.2.1 hα
  · rfl

include hab in
lemma dgGluingCommaPrismPhaseHom_collapsed_zero (hc : I.card ≠ 2)
    (p q : Fin 2) (hpq : p ≤ q) :
    dgCommaAugmentationPrismPhaseHom R C E F (s.pullback α) β
      I a b k hI ha hb hk p q hpq = 0 := by
  have haI : a ∈ I := ha ▸ I.min'_mem (Index.nonempty hI)
  have hbI : b ∈ I := hb ▸ I.max'_mem (Index.nonempty hI)
  have hlt : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
  have hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))) := by
    intro h
    exact (ne_of_lt hlt) (h haI hbI hab)
  fin_cases p <;> fin_cases q
  · change ((dgCommaAugmentationSource R C E F).map _ _).f k _ = 0
    rw [SimplexData.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc, map_zero]
  · change dgCommaAugmentationPrismMixedHom R C E F (s.pullback α) β
      I a b k hI ha hb hk = 0
    rw [dgGluingCommaPrismMixedHom_collapsed R C E F s α β I a b k hI ha hb hk hab,
      SimplexData.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc,
      map_zero, compose_zero]
  · change (1 : ℕ) ≤ 0 at hpq
    omega
  · change ((dgCommaAugmentationTarget R C E F).map _ _).f k _ = 0
    rw [SimplexData.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc, map_zero]

end SerrePositivity.InfinityCategories
