module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismProjectionCoordinates

/-! 相零で第二頂点が相一へ移らなければ、実 prism 成分は replacement 成分そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  {x y : E} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) _⦋n⦌)

lemma dgGluingIdentityCommaPrism_component_inactive
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (hβ : β (J.min' hJ) = 0)
    (hsecond : ∀ h₂ : 2 ≤ J.card, β (second J h₂) ≠ 1) :
    (toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component J k hJ hk =
      dgGluingIdentityCommaReplacementComponent R E s J k hJ hk := by
  apply dgGluingIdentityCommaPrism_component_of_correction_zero R E s β J k hJ hk hβ
  by_cases hJ₂ : 2 ≤ J.card
  · have hs := dgGluingCommaPinchedPrismCorrectionSum_second R E E (DGFunctor.id E) s
      (pinchedPrismPhase β) J hJ₂ k hk
    rw [pinchedPrismPhase_castSucc, ite_eq_right (hsecond hJ₂)] at hs
    exact hs
  · have hc : J.card = 1 := by have := Finset.card_pos.mpr hJ; omega
    exact dgGluingCommaPrismCorrectionSum_card_two R E E (DGFunctor.id E)
      s.val.toSimplexData (pinchedPrismPhase β) (withLast J) (J.min' hJ).castSucc
      (Fin.last (n + 1)) k (two_withLast hJ) (min_withLast hJ _) (max_withLast J _)
      (by rw [card_withLast]; omega) (by rw [card_withLast, hc])

end SerrePositivity.InfinityCategories
