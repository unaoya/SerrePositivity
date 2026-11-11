module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HornPrescribedTopData

/-! 任意に指定した最上位成分と元の全ホーン面を持つ実線形単体。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}
  {n : ℕ} {i : Fin (n + 2)}
  (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y)
  (q : ∀ k : ℤ, k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) →
    _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k)

lemma dgGluingHornTopData_top_equation (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData σ q).component Finset.univ k
      Finset.univ_nonempty hk) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData σ q).rhs Finset.univ k hk := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData_top, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rhs_eq_deleteSum]
  symm
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDeletionSum_target Finset.univ i (Finset.mem_univ _)
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty (by simp) i (Finset.mem_univ _))
    (by have := Finset.card_erase_add_one (Finset.mem_univ i); omega)]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData_missing σ q k hk]
  congr 1
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSolution
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero
  dsimp only
  split_ifs with hJ hkJ
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData_known σ q _ _ hJ hkJ
      (Finset.erase_ssubset (Finset.mem_univ j)).ne
      (fun he => (Finset.mem_erase.mp hj).1
        ((Finset.erase_inj _ (Finset.mem_univ j)).mp he))).symm
  · rfl
  · rfl

lemma dgGluingHornTopData_mem : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData σ q ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearSubmodule R x y (n + 1) := by
  intro J k hJ hk
  by_cases hf : J = Finset.univ
  · subst J
    exact dgGluingHornTopData_top_equation σ q k hk
  · by_cases hm : J = Finset.univ.erase i
    · subst J
      have hkTop : k - 1 = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) := by
        have := Finset.card_erase_add_one (Finset.mem_univ i)
        omega
      have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinched_missing_equation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData σ q)
        Finset.univ (k - 1) (by simp) hkTop i (Finset.mem_univ _)
        (dgGluingHornTopData_top_equation σ q (k - 1) hkTop) (by
          intro j hji
          apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.residual_eq_zero_iff _ _ _ _ _).mpr
          exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHornFilling.equation_of_faces σ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData_face σ q) _ _ _ _
            (Finset.erase_ssubset (Finset.mem_univ j.val)).ne
            (fun he => hji ((Finset.erase_inj _ (Finset.mem_univ j.val)).mp he)))
      have htransport : ∀ (l : ℤ) (hl : l = k)
          (hd : l = 1 - ((Finset.univ.erase i).card : ℤ)),
          (differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData σ q).component (Finset.univ.erase i) l hJ hd) =
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData σ q).rhs (Finset.univ.erase i) l hd) →
          differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData σ q).component (Finset.univ.erase i) k hJ hk) =
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData σ q).rhs (Finset.univ.erase i) k hk := by
        intro l hl
        subst l
        exact fun _ he => he
      exact htransport (k - 1 + 1) (by omega) (by omega) hh
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHornFilling.equation_of_faces σ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData_face σ q) J k hJ hk hf hm

def dgGluingHornTopSimplex : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y (n + 1) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData σ q, dgGluingHornTopData_mem σ q⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
