module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismPhaseCoefficients

/-! 両端相と混合係数の一致を、実 prism の全相の係数へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)

lemma dgGluingCommaPrismPhaseHom_congr {n : ℕ}
    (s : SimplexData R (DGFunctorCommaObject R C E F) n)
    (β γ : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hm : dgCommaAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk =
      dgCommaAugmentationPrismMixedHom R C E F s γ I a b k hI ha hb hk)
    (p q p' q' : Fin 2) (hpq : p ≤ q) (hpq' : p' ≤ q')
    (hp : p = p') (hq : q = q') :
    HEq (dgCommaAugmentationPrismPhaseHom R C E F s β I a b k hI ha hb hk p q hpq)
      (dgCommaAugmentationPrismPhaseHom R C E F s γ I a b k hI ha hb hk p' q' hpq') := by
  subst p'
  subst q'
  fin_cases p <;> fin_cases q
  · rfl
  · exact heq_of_eq hm
  · change (1 : ℕ) ≤ 0 at hpq
    omega
  · rfl

end SerrePositivity.InfinityCategories
