module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HornDeletionEquation

/-! 線形単体は利用可能なホーン面と最上位成分により一意に決まる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}
  {n : ℕ} (i : Fin (n + 2))

lemma dgGluingHornSimplex_zero_missing (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y (n + 1))
    (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ))
    (ht : s.val.component Finset.univ k Finset.univ_nonempty hk = 0)
    (hz : ∀ j : Fin (n + 2), j ≠ i →
      s.val.componentOrZero (Finset.univ.erase j) (k + 1) = 0) :
    s.val.componentOrZero (Finset.univ.erase i) (k + 1) = 0 := by
  have he := s.equation Finset.univ k Finset.univ_nonempty hk
  rw [ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rhs_eq_deleteSum] at he
  change (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d k (k + 1) 0 = _ at he
  rw [map_zero] at he
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deleteSum at he
  rw [Finset.sum_eq_single i] at he
  · have hh := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign Finset.univ i)⁻¹ • z) he.symm
    simpa only [smul_smul, inv_mul_cancel, one_smul, smul_zero] using hh
  · intro j _ hji
    dsimp only
    rw [hz j hji, smul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

lemma dgGluingHornSimplex_ext (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y (n + 1))
    (ht : ∀ k hk, s.val.component Finset.univ k Finset.univ_nonempty hk =
      t.val.component Finset.univ k Finset.univ_nonempty hk)
    (hz : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)),
      J ≠ Finset.univ → J ≠ Finset.univ.erase i →
        s.val.component J k hJ hk = t.val.component J k hJ hk) : s = t := by
  apply sub_eq_zero.mp
  apply Subtype.ext
  funext z
  rcases z with ⟨⟨J, k⟩, hJ, hk⟩
  change k = 1 - (J.card : ℤ) at hk
  change s.val.component J k hJ hk - t.val.component J k hJ hk = 0
  by_cases hf : J = Finset.univ
  · subst J
    exact sub_eq_zero.mpr (ht k hk)
  · by_cases hm : J = Finset.univ.erase i
    · subst J
      have hkTop : k - 1 = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) := by
        have := Finset.card_erase_add_one (Finset.mem_univ i)
        omega
      have he := dgGluingHornSimplex_zero_missing i (s - t) (k - 1) hkTop
        (sub_eq_zero.mpr (ht (k - 1) hkTop)) (by
          intro j hji
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq _ _ _
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty (by simp) j (Finset.mem_univ _))
            (by have := Finset.card_erase_add_one (Finset.mem_univ j); omega)]
          have hh := hz (Finset.univ.erase j) (k - 1 + 1)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty (by simp) j (Finset.mem_univ _))
            (by have := Finset.card_erase_add_one (Finset.mem_univ j); omega)
            (Finset.erase_ssubset (Finset.mem_univ j)).ne
            (fun he => hji ((Finset.erase_inj _ (Finset.mem_univ j)).mp he))
          exact sub_eq_zero.mpr hh)
      have htransport : ∀ (l : ℤ) (hl : l = k),
          (s - t).val.componentOrZero (Finset.univ.erase i) l = 0 →
            s.val.component (Finset.univ.erase i) k hJ hk -
              t.val.component (Finset.univ.erase i) k hJ hk = 0 := by
        intro l hl
        subst l
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq _ _ _ hJ hk]
        exact fun hh => hh
      exact htransport (k - 1 + 1) (by omega) he
    · exact sub_eq_zero.mpr (hz J k hJ hk hf hm)

lemma dgGluingHornData_component_eq_of_faces (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y (n + 1))
    (hfaces : ∀ j : Fin (n + 2), j ≠ i →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom s =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom t)
    (I : Finset (Fin (n + 2))) (k : ℤ) (hI : I.Nonempty) (hk : k = 1 - (I.card : ℤ))
    (hf : I ≠ Finset.univ) (hm : I ≠ Finset.univ.erase i) :
    s.component I k hI hk = t.component I k hI hk := by
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace I i hf hm
  have hji : j ≠ i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_ne I i hf hm
  have hj : j ∉ I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_notMem I i hf hm
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hc : J.card = I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_preimage I j hj
  have hJ : J.Nonempty := Finset.card_pos.mp (by rw [hc]; exact hI.card_pos)
  have hkJ : k = 1 - (J.card : ℤ) := by rw [hc]; exact hk
  have he := congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n => f.component J k hJ hkJ) (hfaces j hji)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn] at he
  have hImage : J.image j.succAboveOrderEmb.toOrderHom = I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I j hj
  simpa only [hImage] using he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
