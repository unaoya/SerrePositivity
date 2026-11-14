module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveListCutSplit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutProduct
/-!
概要：有限切断集合の実合成を、任意の選択点で左右へ分ける。
方針：昇順列を左・選択点・右へ分割し、同じ実列合成の分割へ接続する。
規約：元の同じ実 cochain を使う。使われ方：tensor 候補の合成項と全次元 HA の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 同じ実切断合成を左右の区間へ照合する。 -/
lemma dgNerveCutSort_split {n : ℕ} (S : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ S) :
    S.sort (· ≤ ·) = (S.filter (· < j)).sort (· ≤ ·) ++
      j :: (S.filter (j < ·)).sort (· ≤ ·) := by
  have hsorted : ((S.filter (· < j)).sort (· ≤ ·) ++
      j :: (S.filter (j < ·)).sort (· ≤ ·)).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨(Finset.sortedLT_sort _).pairwise, ?_, ?_⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_, (Finset.sortedLT_sort _).pairwise⟩
      intro x hx
      exact (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hx)).2
    · intro x hx y hy
      have hxj := (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hx)).2
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hxj
      · exact lt_trans hxj (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hy)).2
  apply (Finset.sortedLT_sort S).eq_of_mem_iff hsorted.sortedLT
  intro x
  simp only [Finset.mem_sort, List.mem_append, List.mem_cons, Finset.mem_filter]
  constructor
  · intro hx
    rcases lt_trichotomy x j with h | h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hx, h⟩)
  · rintro (⟨hx, _⟩ | rfl | ⟨hx, _⟩)
    · exact hx
    · exact hj
    · exact hx
/-- 同じ実切断合成を左右の区間へ照合する。 -/
lemma dgNerveCutCard_selected_split {n : ℕ} (S : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ S) :
    S.card = (S.filter (· < j)).card + (S.filter (j < ·)).card + 1 := by
  have h := congrArg List.length (dgNerveCutSort_split S j hj)
  simp only [Finset.length_sort, List.length_append, List.length_cons] at h
  omega
/-- 同じ実切断合成を左右の区間へ照合する。 -/
def dgNerveCutSplitProduct {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b) (hj : j ∈ S) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) (2 - (I.card : ℤ) + (S.card : ℤ)) := by
  have hjI := hc j hj
  let P := I.filter (· ≤ j)
  let Q := I.filter (j ≤ ·)
  have hP : 2 ≤ P.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two ha.1 hjI.1 hjI.2.1
  have hQ : 2 ≤ Q.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hjI.1 hb.1 hjI.2.2
  have haP : IsLeast (P : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_filter.mpr ⟨ha.1, hjI.2.1.le⟩,
      fun _ hx => ha.2 (Finset.mem_filter.mp hx).1⟩
  have hjP : IsGreatest (P : Set (Fin (n + 1))) j :=
    ⟨Finset.mem_filter.mpr ⟨hjI.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
  have hjQ : IsLeast (Q : Set (Fin (n + 1))) j :=
    ⟨Finset.mem_filter.mpr ⟨hjI.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
  have hbQ : IsGreatest (Q : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_filter.mpr ⟨hb.1, hjI.2.2.le⟩,
      fun _ hx => hb.2 (Finset.mem_filter.mp hx).1⟩
  have hcL : ∀ x ∈ S.filter (· < j), x ∈ P ∧ a < x ∧ x < j := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hxj := (Finset.mem_filter.mp hx).2
    exact ⟨Finset.mem_filter.mpr ⟨(hc x hxS).1, hxj.le⟩, (hc x hxS).2.1, hxj⟩
  have hcM : ∀ x ∈ S.filter (j < ·), x ∈ Q ∧ j < x ∧ x < b := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hjx := (Finset.mem_filter.mp hx).2
    exact ⟨Finset.mem_filter.mpr ⟨(hc x hxS).1, hjx.le⟩, hjx, (hc x hxS).2.2⟩
  let left := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D s P a j (S.filter (· < j)) hP haP hjP hcL
  let right := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D s Q j b (S.filter (j < ·)) hQ hjQ hbQ hcM
  exact _root_.SerrePositivity.DifferentialGraded.compose R right left (by
    have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hjI.1
    have ht := dgNerveCutCard_selected_split S j hj
    dsimp only [P, Q]
    omega)
/-- 同じ実切断合成を左右の区間へ照合する。 -/
lemma dgNerveCutProduct_split {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b) (hj : j ∈ S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D s I a b S hI ha hb hc =
      dgNerveCutSplitProduct R D s I a b S j ha hb hc hj := by
  unfold dgNerveCutSplitProduct
  dsimp only
  let L := (S.filter (· < j)).sort (· ≤ ·)
  let M := (S.filter (j < ·)).sort (· ≤ ·)
  have hsort : S.sort (· ≤ ·) = L ++ j :: M := dgNerveCutSort_split S j hj
  have ho : (L ++ j :: M).Pairwise (· < ·) := by
    rw [← hsort]
    exact (Finset.sortedLT_sort S).pairwise
  have hcFull : ∀ x ∈ L ++ j :: M, x ∈ I ∧ a < x ∧ x < b := by
    intro x hx
    rw [← hsort] at hx
    exact hc x ((Finset.mem_sort (· ≤ ·)).mp hx)
  have hk : 2 - (I.card : ℤ) + (S.card : ℤ) =
      2 - (I.card : ℤ) + ((L ++ j :: M).length : ℤ) := by
    rw [← hsort, Finset.length_sort]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_split R D s L M j I a b
    (2 - (I.card : ℤ) + (S.card : ℤ))
    (2 - ((I.filter (· ≤ j)).card : ℤ) + ((S.filter (· < j)).card : ℤ))
    (2 - ((I.filter (j ≤ ·)).card : ℤ) + ((S.filter (j < ·)).card : ℤ))
    hk (by dsimp only [L]; rw [Finset.length_sort])
    (by dsimp only [M]; rw [Finset.length_sort]) hI ha hb
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two ha.1 (hc j hj).1 (hc j hj).2.1)
    ⟨Finset.mem_filter.mpr ⟨ha.1, (hc j hj).2.1.le⟩,
      fun _ hx => ha.2 (Finset.mem_filter.mp hx).1⟩
    ⟨Finset.mem_filter.mpr ⟨(hc j hj).1, le_rfl⟩,
      fun _ hx => (Finset.mem_filter.mp hx).2⟩
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two (hc j hj).1 hb.1 (hc j hj).2.2)
    ⟨Finset.mem_filter.mpr ⟨(hc j hj).1, le_rfl⟩,
      fun _ hx => (Finset.mem_filter.mp hx).2⟩
    ⟨Finset.mem_filter.mpr ⟨hb.1, (hc j hj).2.2.le⟩,
      fun _ hx => hb.2 (Finset.mem_filter.mp hx).1⟩ ho
    (Finset.sortedLT_sort _).pairwise (Finset.sortedLT_sort _).pairwise hcFull
    (by
      intro x hx
      have hxS := (Finset.mem_sort (· ≤ ·)).mp hx
      have hxj := (Finset.mem_filter.mp hxS).2
      have hxI := hc x (Finset.mem_filter.mp hxS).1
      exact ⟨Finset.mem_filter.mpr ⟨hxI.1, hxj.le⟩, hxI.2.1, hxj⟩)
    (by
      intro x hx
      have hxS := (Finset.mem_sort (· ≤ ·)).mp hx
      have hjx := (Finset.mem_filter.mp hxS).2
      have hxI := hc x (Finset.mem_filter.mp hxS).1
      exact ⟨Finset.mem_filter.mpr ⟨hxI.1, hjx.le⟩, hjx, hxI.2.2⟩)
    (by
      have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card (hc j hj).1
      have ht := dgNerveCutCard_selected_split S j hj
      omega)
  have hFull : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D s I a b S hI ha hb hc)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s I a b (L ++ j :: M)
        (2 - (I.card : ℤ) + (S.card : ℤ)) hk hI ha hb ho hcFull) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s rfl rfl rfl hsort rfl
  exact eq_of_heq (hFull.trans (heq_of_eq h))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
