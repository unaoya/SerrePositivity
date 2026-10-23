module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaCollapsedUnit

/-! 相零の終端以前には補正がなく、恒等 augmentation の主項は元の replacement 係数。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve

lemma dgGluingCommaPrismMixedHom_terminal_zero
    (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
    (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
    {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hβ : β b = 0) :
    dgCommaAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk =
      compose R (dgCommaAugmentationComponent R C E F (s.obj b)).val
        (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
          (s.hom I a b k hI ha hb hk)) (add_zero k) := by
  unfold dgCommaAugmentationPrismMixedHom
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  rintro ⟨j, hj⟩ _
  split_ifs with h
  · have hle := β.monotone h.2.1.le
    rw [hβ, h.2.2] at hle
    change (1 : ℕ) ≤ 0 at hle
    omega
  · rfl

lemma dgGluingIdentityCommaMain_coefficient
    (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
    {X Y : DGFunctorCommaObject R E E (DGFunctor.id E)}
    (y : E) (hY : Y = dgGluingIdentityCommaObject R E y) {k : ℤ}
    (f : GradedHom R X Y k) :
    HEq (compose R (dgCommaAugmentationComponent R E E (DGFunctor.id E) Y).val
      (((dgCommaAugmentationSource R E E (DGFunctor.id E)).map X Y).f k f) (add_zero k))
      (((dgCommaAugmentationSource R E E (DGFunctor.id E)).map X Y).f k f) := by
  subst Y
  change HEq (compose R (unitElement R y).val _ (add_zero k)) _
  exact heq_of_eq (unit_compose R _)

end SerrePositivity.InfinityCategories
