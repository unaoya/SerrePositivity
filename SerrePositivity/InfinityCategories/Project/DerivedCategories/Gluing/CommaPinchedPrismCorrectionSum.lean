module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPinchedPrismCutZero

/-! augmentation の混合係数の実切断和は、pinched 入力で唯一の第二切断へ縮退する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ}

def dgGluingCommaPrismCorrectionSum (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :=
  ∑ j : I, if h : a < j.val ∧ j.val < b ∧ β j.val = 1 then
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCut R C E F s I a b k hI ha hb hk j.val j.property h.1 h.2.1
    else 0

variable {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) X Y) _⦋n⦌)

lemma dgGluingCommaPinchedPrismCorrectionSum_second
    (β : Fin (n + 2) →o Fin 2) (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    dgGluingCommaPrismCorrectionSum R C E F s.val.toSimplexData β (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
      (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)).castSucc (Fin.last (n + 1)) k
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega) =
    if β (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ).castSucc = 1 then
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCut R C E F s.val.toSimplexData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
        (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)).castSucc (Fin.last (n + 1)) k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ).castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_, (Finset.mem_erase.mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second_mem_erase J hJ)).2, rfl⟩))
        (Fin.castSucc_lt_castSucc_iff.mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.first_lt_second J hJ)) (Fin.castSucc_lt_last _)
      else 0 := by
  let j₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J := ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ).castSucc,
    Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨_, (Finset.mem_erase.mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second_mem_erase J hJ)).2, rfl⟩)⟩
  dsimp only [dgGluingCommaPrismCorrectionSum]
  rw [Finset.sum_eq_single j₀]
  · by_cases hβ : β (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ).castSucc = 1
    · simp only [j₀, Fin.castSucc_lt_castSucc_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.first_lt_second, Fin.castSucc_lt_last,
        hβ, and_self, dite_true, ite_true]
    · simp only [j₀, hβ, and_false, dite_false, ite_false]
  · rintro ⟨j, hj⟩ _ hne
    split_ifs with h
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h.2.1)
      have hjJ : j ∈ J := by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast, Finset.mem_insert, Finset.mem_image,
        Fin.castSucc_inj, Fin.castSucc_ne_last, false_or, exists_eq_right] using hj
      have hne' : j ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ := by
        intro he
        apply hne
        apply Subtype.ext
        exact congrArg Fin.castSucc he
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPinchedPrismCut_zero_of_ne_second R C E F s J hJ k hk j hjJ
        (Fin.castSucc_lt_castSucc_iff.mp h.1) hne'
    · rfl
  · intro h
    exact False.elim (h (Finset.mem_univ j₀))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
