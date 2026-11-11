module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra
/-!
概要：指定した昇順の切断点に沿い、同じ部分 Hom 成分の合成 cochain を実再帰で作る。
方針：指定次数とその式を保持し、列の先頭で区切る再帰と実成分の次数比較を使う。
規約：入力の Small 性・Hom の平坦性は不要。使われ方：dg nerve の tensor 候補。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 同じ指定次数の実切断合成またはその空・一切断の式。 -/
def dgNerveListCutProduct {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (L : List (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (L.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) k := by
  cases L with
  | nil =>
    exact s.hom I a b _ hI
      (ha.unique (Finset.isLeast_min' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)))
      (hb.unique (Finset.isGreatest_max' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)))
        (by simpa only [List.length_nil, Nat.cast_zero, add_zero] using hk)
  | cons j L =>
    have hj := hc j (by simp)
    have hp := List.pairwise_cons.mp ho
    let P := I.filter (· ≤ j)
    let Q := I.filter (j ≤ ·)
    have hP : 2 ≤ P.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two ha.1 hj.1 hj.2.1
    have hQ : 2 ≤ Q.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj.1 hb.1 hj.2.2
    have hjQ : IsLeast (Q : Set (Fin (n + 1))) j :=
      ⟨Finset.mem_filter.mpr ⟨hj.1, le_rfl⟩, fun _ hk => (Finset.mem_filter.mp hk).2⟩
    have hbQ : IsGreatest (Q : Set (Fin (n + 1))) b :=
      ⟨Finset.mem_filter.mpr ⟨hb.1, hj.2.2.le⟩,
        fun _ hk => hb.2 (Finset.mem_filter.mp hk).1⟩
    have ht : ∀ k ∈ L, k ∈ Q ∧ j < k ∧ k < b := by
      intro k hk
      have hkI := hc k (List.mem_cons_of_mem j hk)
      have hjk := hp.1 k hk
      exact ⟨Finset.mem_filter.mpr ⟨hkI.1, hjk.le⟩, hjk, hkI.2.2⟩
    let first := s.hom P a j (2 - (P.card : ℤ)) hP
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ha hj.2.1.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)) rfl
    let rest := dgNerveListCutProduct s Q j b L
      (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht
    exact compose R rest first (by
      have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj.1
      dsimp only [P, Q]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
      omega)
termination_by L.length
end SerrePositivity.InfinityCategories.Project.DerivedCategories
