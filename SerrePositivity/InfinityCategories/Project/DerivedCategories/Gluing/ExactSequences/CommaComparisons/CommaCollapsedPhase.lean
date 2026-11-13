module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CommaComparisons.CommaCollapsedPrimitive
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugPrismPhaseCoefficients

/-! 全て同じ頂点へ潰れた部分では、任意相の混合係数は元の主項だけになる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
  (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (m + 1) →o Fin 2)
  (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
  (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
  (hk : k = 2 - (I.card : ℤ)) (hab : α a = α b)

include hab in
lemma dgGluingCommaPrismMixedHom_collapsed :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F (s.pullback α) β I a b k hI ha hb hk =
      compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R C E F (s.obj (α b))).val
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj (α a)) (s.obj (α b))).f k
          ((s.pullback α).hom I a b k hI ha hb hk)) (add_zero k) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom
  let z := compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R C E F (s.obj (α b))).val
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj (α a)) (s.obj (α b))).f k
      ((s.pullback α).hom I a b k hI ha hb hk)) (add_zero k)
  change z + _ = z
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  rintro ⟨j, hj⟩ _
  split_ifs with h
  · have hα : α j = α b := le_antisymm (α.monotone h.2.1.le)
      (hab ▸ α.monotone h.1.le)
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismCut_pullback_collapsed R C E F s α
      I a b k hI ha hb hk j hj h.1 h.2.1 hα
  · rfl

include hab in
lemma dgGluingCommaPrismPhaseHom_collapsed_zero (hc : I.card ≠ 2)
    (p q : Fin 2) (hpq : p ≤ q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismPhaseHom R C E F (s.pullback α) β
      I a b k hI ha hb hk p q hpq = 0 := by
  have haI : a ∈ I := ha ▸ I.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
  have hbI : b ∈ I := hb ▸ I.max'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
  have hlt : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
  have hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))) := by
    intro h
    exact (ne_of_lt hlt) (h haI hbI hab)
  fin_cases p <;> fin_cases q
  · change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map _ _).f k _ = 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc, map_zero]
  · change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F (s.pullback α) β
      I a b k hI ha hb hk = 0
    rw [dgGluingCommaPrismMixedHom_collapsed R C E F s α β I a b k hI ha hb hk hab,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc,
      map_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero]
  · change (1 : ℕ) ≤ 0 at hpq
    omega
  · change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R C E F).map _ _).f k _ = 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc, map_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
