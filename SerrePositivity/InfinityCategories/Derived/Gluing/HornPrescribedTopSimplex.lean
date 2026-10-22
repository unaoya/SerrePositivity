module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HornPrescribedTopData

/-! 任意に指定した最上位成分と元の全ホーン面を持つ実線形単体。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}
  {n : ℕ} {i : Fin (n + 2)}
  (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ DGNerve.pinchedHom R D x y)
  (q : ∀ k : ℤ, k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) →
    GradedHom R x y k)

lemma dgGluingHornTopData_top_equation (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    differential R ((dgGluingHornTopData σ q).component Finset.univ k
      Finset.univ_nonempty hk) = (dgGluingHornTopData σ q).rhs Finset.univ k hk := by
  rw [dgGluingHornTopData_top, LinearData.rhs_eq_deleteSum]
  symm
  apply dgGluingDeletionSum_target Finset.univ i (Finset.mem_univ _)
  dsimp only
  rw [LinearData.componentOrZero_eq _ _ _
    (LinearData.erase_nonempty (by simp) i (Finset.mem_univ _))
    (by have := Finset.card_erase_add_one (Finset.mem_univ i); omega)]
  rw [dgGluingHornTopData_missing σ q k hk]
  congr 1
  unfold deletionSolution
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold LinearData.componentOrZero
  dsimp only
  split_ifs with hJ hkJ
  · exact (dgGluingHornTopData_known σ q _ _ hJ hkJ
      (Finset.erase_ssubset (Finset.mem_univ j)).ne
      (fun he => (Finset.mem_erase.mp hj).1
        ((Finset.erase_inj _ (Finset.mem_univ j)).mp he))).symm
  · rfl
  · rfl

lemma dgGluingHornTopData_mem : dgGluingHornTopData σ q ∈ linearSubmodule R x y (n + 1) := by
  intro J k hJ hk
  by_cases hf : J = Finset.univ
  · subst J
    exact dgGluingHornTopData_top_equation σ q k hk
  · by_cases hm : J = Finset.univ.erase i
    · subst J
      have hkTop : k - 1 = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) := by
        have := Finset.card_erase_add_one (Finset.mem_univ i)
        omega
      have hh := dgGluingPinched_missing_equation (dgGluingHornTopData σ q)
        Finset.univ (k - 1) (by simp) hkTop i (Finset.mem_univ _)
        (dgGluingHornTopData_top_equation σ q (k - 1) hkTop) (by
          intro j hji
          apply (LinearData.residual_eq_zero_iff _ _ _ _ _).mpr
          exact HornData.equation_of_faces σ _ (dgGluingHornTopData_face σ q) _ _ _ _
            (Finset.erase_ssubset (Finset.mem_univ j.val)).ne
            (fun he => hji ((Finset.erase_inj _ (Finset.mem_univ j.val)).mp he)))
      have htransport : ∀ (l : ℤ) (hl : l = k)
          (hd : l = 1 - ((Finset.univ.erase i).card : ℤ)),
          (differential R ((dgGluingHornTopData σ q).component (Finset.univ.erase i) l hJ hd) =
            (dgGluingHornTopData σ q).rhs (Finset.univ.erase i) l hd) →
          differential R ((dgGluingHornTopData σ q).component (Finset.univ.erase i) k hJ hk) =
            (dgGluingHornTopData σ q).rhs (Finset.univ.erase i) k hk := by
        intro l hl
        subst l
        exact fun _ he => he
      exact htransport (k - 1 + 1) (by omega) (by omega) hh
    · exact HornData.equation_of_faces σ _ (dgGluingHornTopData_face σ q) J k hJ hk hf hm

def dgGluingHornTopSimplex : LinearSimplex R x y (n + 1) :=
  ⟨dgGluingHornTopData σ q, dgGluingHornTopData_mem σ q⟩

end SerrePositivity.InfinityCategories
