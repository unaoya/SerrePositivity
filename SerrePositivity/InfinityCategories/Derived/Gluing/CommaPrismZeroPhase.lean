module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPinchedPrismMixedCoefficient
public import SerrePositivity.InfinityCategories.Derived.PinchedPrismPhase

/-! 標的だけ相一の prism では内部切断の相は零であり、全補正和が消える。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) (n + 1))

lemma dgGluingCommaPrismCorrectionSum_zeroPhase
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    dgGluingCommaPrismCorrectionSum R C E F s
      (pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) I a b k hI ha hb hk = 0 := by
  dsimp only [dgGluingCommaPrismCorrectionSum]
  apply Finset.sum_eq_zero
  rintro ⟨j, hj⟩ _
  split_ifs with h
  · have hjlast : j ≠ Fin.last (n + 1) := ne_of_lt (h.2.1.trans_le (Fin.le_last b))
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hjlast
    have hz := pinchedPrismPhase_castSucc
      (OrderHom.const (Fin (n + 1)) (0 : Fin 2)) j
    have hf : (0 : Fin 2) = 1 := hz.symm.trans h.2.2
    exact False.elim (Fin.zero_ne_one hf)
  · rfl

lemma dgGluingCommaPrismMixedHom_zeroPhase
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    dgCommaAugmentationPrismMixedHom R C E F s
      (pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) I a b k hI ha hb hk =
        dgGluingCommaPrismMainCoefficient R C E F s I a b k hI ha hb hk := by
  rw [dgGluingCommaPrismMixedCoefficient_eq,
    dgGluingCommaPrismCorrectionSum_zeroPhase R C E F s I a b k hI ha hb hk, add_zero]

end SerrePositivity.InfinityCategories
