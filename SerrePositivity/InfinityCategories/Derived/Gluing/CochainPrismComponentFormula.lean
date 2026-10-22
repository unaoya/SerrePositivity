module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainIdentityCommaInputComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismInactiveComponent
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainDegreeHEq

/-! 明示 cochain prism の全線形成分は、二端点と同じ一切断の負 cochain で決まる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [DGCategory R C] [DGCategory R E]
  {a b : C} (x y : E) (f g : homObject R C a b ⟶ homObject R E x y)
  (h : Cochain (homObject R C a b) (homObject R E x y) (-1))
  (he : δ (-1) 0 h = Cochain.ofHom (g - f)) {n : ℕ}
  (s : (DGNerve.pinchedHom R C a b) _⦋n⦌)
local notation "F" => dgGluingCochainIdentityCommaLift R E x y (homObject R C a b) f g h he
local notation "t" => pinchedHomChainMapSimplex F s

def dgGluingCochainPrismCorrectionValue (β : Fin (n + 1) →o Fin 2)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) : GradedHom R x y k :=
  if h₂ : 2 ≤ J.card then
    if β (second J h₂) = 1 then
      (((withLast J).filter ((second J h₂).castSucc < ·)).card : ℤ).negOnePow •
        -h.v (k + 1) k (by omega)
          ((toLinearData s).component (J.erase (J.min' (Index.nonempty h₂))) (k + 1)
            (LinearData.erase_nonempty h₂ _ (J.min'_mem _))
            (by have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty h₂)); omega))
    else 0
  else 0

lemma dgGluingCochainPrism_component_formula
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E t β)).component J k hJ hk =
      if β (J.min' hJ) = 1 then g.f k ((toLinearData s).component J k hJ hk)
      else f.f k ((toLinearData s).component J k hJ hk) +
        dgGluingCochainPrismCorrectionValue R C E x y h s β J k hk := by
  by_cases hone : β (J.min' hJ) = 1
  · rw [ite_eq_left hone, dgGluingIdentityCommaPrism_component_one R E t J k hJ hk β hone]
    exact dgGluingCochainIdentityCommaInput_source R C E x y f g h he s J k hJ hk
  · rw [ite_eq_right hone]
    have hzero : β (J.min' hJ) = 0 := by omega
    by_cases hactive : ∃ h₂ : 2 ≤ J.card, β (second J h₂) = 1
    · obtain ⟨h₂, hsecond⟩ := hactive
      rw [dgGluingCochainPrismCorrectionValue, dite_eq_left h₂, ite_eq_left hsecond]
      have hd := dgGluingIdentityCommaPrism_component_correction R E t β J h₂ k hk hzero hsecond
      rw [dgGluingCochainIdentityCommaInput_primitive] at hd
      have hh := dgGluingCochain_neg_smul_heq h (p := k + 1) (q := k + 1 - 1) (q' := k)
        (by omega) ((toLinearData s).component (J.erase (J.min' (Index.nonempty h₂)))
          (k + 1) (LinearData.erase_nonempty h₂ _ (J.min'_mem _))
          (by have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty h₂)); omega))
        (by omega) (by omega)
        ((((withLast J).filter ((second J h₂).castSucc < ·)).card : ℤ).negOnePow)
      have heq := eq_of_heq (hd.trans hh)
      rw [dgGluingCochainIdentityCommaInput_replacement] at heq
      have ha := congrArg (fun z : GradedHom R x y k =>
        z + f.f k ((toLinearData s).component J k hJ hk)) heq
      simp only [sub_add_cancel] at ha
      exact ha.trans (add_comm _ _)
    · have hsecond : ∀ h₂ : 2 ≤ J.card, β (second J h₂) ≠ 1 := by
        simpa only [not_exists] using hactive
      rw [dgGluingIdentityCommaPrism_component_inactive R E t β J k hJ hk hzero hsecond,
        dgGluingCochainIdentityCommaInput_replacement]
      by_cases h₂ : 2 ≤ J.card
      · rw [dgGluingCochainPrismCorrectionValue, dite_eq_left h₂,
          ite_eq_right (hsecond h₂), add_zero]
      · rw [dgGluingCochainPrismCorrectionValue, dite_eq_right h₂, add_zero]

end SerrePositivity.InfinityCategories
