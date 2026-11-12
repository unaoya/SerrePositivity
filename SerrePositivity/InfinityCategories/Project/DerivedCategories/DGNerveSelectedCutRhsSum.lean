module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveSelectedCutIndex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutBoundaryFirstSum
/-!
概要：第一選択成分の HA 右辺と実微分を、同じ選択点の有限和へ展開する。
方針：元の HA 項、選択点の有限和、第二切断合成の実微分の同定を使う。
規約：同じ実 cochain を使う。使われ方：tensor 候補の全 HA の有限和の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 元の実成分の微分と有限和の照合。 -/
def dgNerveSelectedCutTerm {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (a b : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hab : a < b)
    (hc : ∀ x ∈ S, a < x ∧ x < b) (j : Fin (n + 1)) (hj : j ∈ S) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) (-(S.card : ℤ) + 1) := by
  let J := insert a (insert b S)
  have hcard : J.card = S.card + 2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutIndex_card S a b hab hc
  have hJ : 2 ≤ J.card := by omega
  have haJ : IsLeast (J : Set (Fin (n + 1))) a := by
    refine ⟨by simp [J], ?_⟩
    intro x hx
    change x ∈ J at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hab.le
      · exact (hc x hx).1.le
  have hbJ : IsGreatest (J : Set (Fin (n + 1))) b := by
    refine ⟨by simp [J], ?_⟩
    intro x hx
    change x ∈ J at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hab.le
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (hc x hx).2.le
  exact s.term J a b (-(S.card : ℤ)) hJ
    (haJ.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)))
    (hbJ.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))) (by omega)
    j (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)) (hc j hj).1 (hc j hj).2
/-- 元の実成分の微分と有限和の照合。 -/
lemma dgNerveSelectedCutRhs_eq_sum {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (a b : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hab : a < b) (hc : ∀ x ∈ S, a < x ∧ x < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutRhs R D s a b S hab hc =
      ∑ j : S, dgNerveSelectedCutTerm R D s a b S hab hc j.val j.property := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutRhs dgNerveSelectedCutTerm
  dsimp only
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveFiniteSubset_sum (insert a (insert b S)), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveFiniteSubset_sum S]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hjS : j ∈ S
  · have hjJ : j ∈ insert a (insert b S) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hjS)
    have hinner := hc j hjS
    simp only [dite_eq_left hjJ, dite_eq_left hinner, dite_eq_left hjS]
  · by_cases hjJ : j ∈ insert a (insert b S)
    · have hnot : ¬(a < j ∧ j < b) := by
        intro h
        rcases Finset.mem_insert.mp hjJ with hja | hjJ
        · exact (ne_of_lt h.1) hja.symm
        · rcases Finset.mem_insert.mp hjJ with hjb | hjJ
          · exact (ne_of_lt h.2) hjb
          · exact hjS hjJ
      simp only [dite_eq_left hjJ, dite_eq_right hnot, dite_eq_right hjS]
    · simp only [dite_eq_right hjJ, dite_eq_right hjS]
/-- 元の実成分の微分と有限和の照合。 -/
lemma dgNerveSelectedCutHom_differential_eq_sum {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n)
    (a b : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hab : a < b)
    (hc : ∀ x ∈ S, a < x ∧ x < b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutHom R D s.toSimplexData a b S hab hc) =
      ∑ j : S, dgNerveSelectedCutTerm R D s.toSimplexData a b S hab hc j.val j.property := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutHom_differential, dgNerveSelectedCutRhs_eq_sum]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
