module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPinchedPrismCutZero

/-! augmentation の混合係数の実切断和は、pinched 入力で唯一の第二切断へ縮退する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ}

def dgGluingCommaPrismCorrectionSum (s : SimplexData R (DGFunctorCommaObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :=
  ∑ j : I, if h : a < j.val ∧ j.val < b ∧ β j.val = 1 then
    dgCommaAugmentationPrismCut R C E F s I a b k hI ha hb hk j.val j.property h.1 h.2.1
    else 0

variable {X Y : DGFunctorCommaObject R C E F}
  (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R C E F) X Y) _⦋n⦌)

lemma dgGluingCommaPinchedPrismCorrectionSum_second
    (β : Fin (n + 2) →o Fin 2) (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    dgGluingCommaPrismCorrectionSum R C E F s.val.toSimplexData β (withLast J)
      (J.min' (Index.nonempty hJ)).castSucc (Fin.last (n + 1)) k
      (two_withLast (Index.nonempty hJ)) (min_withLast (Index.nonempty hJ) _)
      (max_withLast J _) (by rw [card_withLast]; omega) =
    if β (second J hJ).castSucc = 1 then
      dgCommaAugmentationPrismCut R C E F s.val.toSimplexData (withLast J)
        (J.min' (Index.nonempty hJ)).castSucc (Fin.last (n + 1)) k
        (two_withLast (Index.nonempty hJ)) (min_withLast (Index.nonempty hJ) _)
        (max_withLast J _) (by rw [card_withLast]; omega)
        (second J hJ).castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩))
        (Fin.castSucc_lt_castSucc_iff.mpr (first_lt_second J hJ)) (Fin.castSucc_lt_last _)
      else 0 := by
  let j₀ : withLast J := ⟨(second J hJ).castSucc,
    Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩)⟩
  dsimp only [dgGluingCommaPrismCorrectionSum]
  rw [Finset.sum_eq_single j₀]
  · by_cases hβ : β (second J hJ).castSucc = 1
    · simp only [j₀, Fin.castSucc_lt_castSucc_iff, first_lt_second, Fin.castSucc_lt_last,
        hβ, and_self, dite_true, ite_true]
    · simp only [j₀, hβ, and_false, dite_false, ite_false]
  · rintro ⟨j, hj⟩ _ hne
    split_ifs with h
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h.2.1)
      have hjJ : j ∈ J := by simpa only [withLast, Finset.mem_insert, Finset.mem_image,
        Fin.castSucc_inj, Fin.castSucc_ne_last, false_or, exists_eq_right] using hj
      have hne' : j ≠ second J hJ := by
        intro he
        apply hne
        apply Subtype.ext
        exact congrArg Fin.castSucc he
      exact dgGluingCommaPinchedPrismCut_zero_of_ne_second R C E F s J hJ k hk j hjJ
        (Fin.castSucc_lt_castSucc_iff.mp h.1) hne'
    · rfl
  · intro h
    exact False.elim (h (Finset.mem_univ j₀))

end SerrePositivity.InfinityCategories
