module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutLeibniz
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutSplit
/-!
概要：元の実切断合成から、未選択内部点の削除・追加の符号付き和を作る。
方針：同じ指定次数の切断合成を使い、空切断では元の HA 右辺へ照合する。
規約：同じ実 cochain を使う。使われ方：第二因子の全 HA 展開と tensor 候補の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 元の実切断成分と符号付き境界の照合。 -/
def dgNerveCutBoundaryTerm {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (S.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b)
    (hj : j ∈ I) (haj : a < j) (hjb : j < b) (hjS : j ∉ S) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) (k + 1) := by
  have hE : 2 ≤ (I.erase j).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two ha.1 hb.1 haj hjb
  have haE : IsLeast ((I.erase j) : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_erase.mpr ⟨ne_of_lt haj, ha.1⟩,
      fun _ hx => ha.2 (Finset.mem_erase.mp hx).2⟩
  have hbE : IsGreatest ((I.erase j) : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hjb), hb.1⟩,
      fun _ hx => hb.2 (Finset.mem_erase.mp hx).2⟩
  have hcE : ∀ x ∈ S.sort (· ≤ ·), x ∈ I.erase j ∧ a < x ∧ x < b := by
    intro x hx
    have hxS := (Finset.mem_sort (· ≤ ·)).mp hx
    have hxI := hc x hxS
    exact ⟨Finset.mem_erase.mpr ⟨fun hxj => hjS (hxj ▸ hxS), hxI.1⟩, hxI.2⟩
  have hcA : ∀ x ∈ (insert j S).sort (· ≤ ·), x ∈ I ∧ a < x ∧ x < b := by
    intro x hx
    rcases Finset.mem_insert.mp ((Finset.mem_sort (· ≤ ·)).mp hx) with rfl | hx
    · exact ⟨hj, haj, hjb⟩
    · exact hc x hx
  have hI : 2 ≤ I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.two_le_card ha.1 hb.1 (ne_of_lt (lt_trans haj hjb))
  let deleted := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s (I.erase j) a b (S.sort (· ≤ ·))
    (k + 1) (by
      rw [Finset.length_sort]
      have hcard := Finset.card_erase_add_one hj
      omega) hE haE hbE (Finset.sortedLT_sort S).pairwise hcE
  let added := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s I a b ((insert j S).sort (· ≤ ·))
    (k + 1) (by
      rw [Finset.length_sort, Finset.card_insert_of_notMem hjS]
      push_cast
      omega) hI ha hb (Finset.sortedLT_sort (insert j S)).pairwise hcA
  exact (((I.filter (j < ·)).card : ℤ) - ((S.filter (j < ·)).card : ℤ)).negOnePow •
    (deleted - added)
/-- 元の実切断成分と符号付き境界の照合。 -/
def dgNerveCutBoundarySum {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (S.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) (k + 1) :=
  ∑ j : I, if h : a < j.val ∧ j.val < b ∧ j.val ∉ S then
    dgNerveCutBoundaryTerm R D s I a b S j.val k hk ha hb hc j.property h.1 h.2.1 h.2.2 else 0
/-- 元の実切断成分と符号付き境界の照合。 -/
lemma dgNerveCutBoundaryTerm_empty {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b j : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    dgNerveCutBoundaryTerm R D s I a b ∅ j k (by simpa using hk) ha hb (by simp)
      hj haj hjb (by simp) =
      s.term I a b k hI (ha.unique (Finset.isLeast_min' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)))
        (hb.unique (Finset.isGreatest_max' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))) hk j hj haj hjb := by
  unfold dgNerveCutBoundaryTerm _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term
  dsimp only
  simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, sub_zero,
    Finset.sort_empty, Finset.insert_empty, Finset.sort_singleton]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_nil R D s (I.erase j) a b (k + 1) (by
    have hcard := Finset.card_erase_add_one hj
    omega)]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_singleton R D s I a b j (k + 1) (by omega)
    hI ha hb hj haj hjb]
/-- 元の実切断成分と符号付き境界の照合。 -/
lemma dgNerveCutBoundarySum_empty {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    dgNerveCutBoundarySum R D s I a b ∅ k (by simpa using hk) ha hb (by simp) =
      s.rhs I a b k hI (ha.unique (Finset.isLeast_min' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)))
        (hb.unique (Finset.isGreatest_max' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))) hk := by
  unfold dgNerveCutBoundarySum _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : a < j.val ∧ j.val < b
  · have h' : a < j.val ∧ j.val < b ∧ j.val ∉ (∅ : Finset (Fin (n + 1))) :=
      ⟨h.1, h.2, by simp⟩
    rw [dite_eq_left h', dite_eq_left h]
    exact dgNerveCutBoundaryTerm_empty R D s I a b j.val k hk hI ha hb j.property h.1 h.2
  · have h' : ¬(a < j.val ∧ j.val < b ∧ j.val ∉ (∅ : Finset (Fin (n + 1)))) :=
      fun h' => h ⟨h'.1, h'.2.1⟩
    rw [dite_eq_right h', dite_eq_right h]
/-- 元の実切断成分と符号付き境界の照合。 -/
lemma dgNerveCutRhs_empty_eq_boundarySum {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRhs R D s I a b ∅ hI ha hb (by simp) =
      dgNerveCutBoundarySum R D s I a b ∅
        (2 - (I.card : ℤ) + ((∅ : Finset (Fin (n + 1))).card : ℤ))
        rfl ha hb (by simp) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRhs
  simp only [Finset.sort_empty]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutRhs]
  dsimp only [List.casesOn]
  exact (dgNerveCutBoundarySum_empty R D s I a b _ (by simp) hI ha hb).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
