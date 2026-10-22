module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismLinearCorrection
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrismCorrectionEdge

/-! 同じ入力上で二射影が一致し primitive が消えれば、明示 prism の全係数は時間に定値。 -/
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
  {Q : Complex R} (q : homObject R E x y ⟶ Q)
  (hprim : ∀ J p hJ hp,
    q.f (p - 1) (dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E)
      (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) p
      ((toLinearData s).component J p hJ hp)) = 0)
  (hpair : ∀ J k hJ hk,
    q.f k (dgGluingIdentityCommaSourceComponent R E s J k hJ hk) =
      q.f k (dgGluingIdentityCommaReplacementComponent R E s J k hJ hk))

include hprim hpair in
lemma dgGluingIdentityCommaPrism_component_post_zero
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    q.f k ((toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component
        J k hJ hk) = q.f k (dgGluingIdentityCommaReplacementComponent R E s J k hJ hk) := by
  have hf : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rcases hf (β (J.min' hJ)) with hzero | hone
  · by_cases hJ₂ : 2 ≤ J.card
    · by_cases hsecond : β (second J hJ₂) = 1
      · have hd := dgGluingIdentityCommaPrism_component_correction R E s β J hJ₂ k hk
          hzero hsecond
        have hz := dgGluingComplexMap_zero_of_scalar_heq q (by omega) _ _ _ hd
          (hprim (J.erase (J.min' (Index.nonempty hJ₂))) (k + 1) _ _)
        rw [map_sub] at hz
        exact sub_eq_zero.mp hz
      · have hs := dgGluingCommaPinchedPrismCorrectionSum_second R E E (DGFunctor.id E) s
          (pinchedPrismPhase β) J hJ₂ k hk
        rw [pinchedPrismPhase_castSucc, ite_eq_right hsecond] at hs
        exact congrArg (fun z : GradedHom R x y k => q.f k z)
          (dgGluingIdentityCommaPrism_component_of_correction_zero R E s β J k hJ hk hzero hs)
    · have hc : J.card = 1 := by have := Finset.card_pos.mpr hJ; omega
      have hs := dgGluingCommaPrismCorrectionSum_card_two R E E (DGFunctor.id E)
        s.val.toSimplexData (pinchedPrismPhase β) (withLast J) (J.min' hJ).castSucc
        (Fin.last (n + 1)) k (two_withLast hJ) (min_withLast hJ _) (max_withLast J _)
        (by rw [card_withLast]; omega) (by rw [card_withLast, hc])
      exact congrArg (fun z : GradedHom R x y k => q.f k z)
        (dgGluingIdentityCommaPrism_component_of_correction_zero R E s β J k hJ hk hzero hs)
  · rw [dgGluingIdentityCommaPrism_component_one R E s J k hJ hk β hone]
    exact hpair J k hJ hk

end SerrePositivity.InfinityCategories
