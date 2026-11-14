module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorFixedFirst
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveListCutHEq
/-!
概要：定値単体の任意切断合成は、非零次数で零、零次数で同じ単位になる。
方針：選択列の長さを区間の濃度で抑え、一段の合成と実単位則で帰納する。
規約：同じ実 cochain を全次数で比較する。使われ方：固定終域の全単体比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators _root_.Simplicial
/-- 定値入力の同じ実切断合成と次数による零・単位の判定。 -/
lemma dgNerveListCutLength_le {n : ℕ}
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (L : List (Fin (n + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) : L.length + 2 ≤ I.card := by
  have hab : a < b := by
    have h := I.min'_lt_max'_of_card (by omega)
    simpa only [← ha.unique (I.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)),
      ← hb.unique (I.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))] using h
  have hJI : insert a (insert b L.toFinset) ⊆ I := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ha.1
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hb.1
    exact (hc j (List.mem_toFinset.mp hj)).1
  have hcard := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutIndex_card L.toFinset a b hab
    (fun j hj => (hc j (List.mem_toFinset.mp hj)).2)
  have hle := Finset.card_le_card hJI
  have hlen : L.toFinset.card = L.length := List.toFinset_card_of_nodup ho.nodup
  omega
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 定値入力の同じ実切断合成と次数による零・単位の判定。 -/
lemma dgNerveListCutProduct_constant_zero {n : ℕ} (x : D)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (L : List (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (L.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) (hk0 : k ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
      I a b L k hk hI ha hb ho hc = 0 := by
  induction L generalizing I a b k with
  | nil =>
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
    dsimp only [List.casesOn]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_hom_zero
    intro he
    apply hk0
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hk
    omega
  | cons j L ih =>
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
    by_cases hP2 : P.card = 2
    · have hq0 : 2 - (Q.card : ℤ) + (L.length : ℤ) ≠ 0 := by
        have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj.1
        dsimp only [P, Q] at hP2 ⊢
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
        omega
      have hr := ih Q j b (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht hq0
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
      dsimp only [List.casesOn]
      rw [hr, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
    · have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_hom_zero (A := R) x P a j (2 - (P.card : ℤ)) hP
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ha hj.2.1.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)) rfl hP2
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
      dsimp only [List.casesOn]
      rw [hz, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero]
/-- 定値入力の同じ実切断合成と次数による零・単位の判定。 -/
lemma dgNerveListCutProduct_constant_unit {n : ℕ} (x : D)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (L : List (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (L.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) (hk0 : k = 0) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
      I a b L k hk hI ha hb ho hc) (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val := by
  induction L generalizing I a b k with
  | nil =>
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
    dsimp only [List.casesOn]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_hom_unit (A := R) x I a b k hI _ _ _ (by
      simp only [List.length_nil, Nat.cast_zero, add_zero] at hk
      omega)
  | cons j L ih =>
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
    have hlen := dgNerveListCutLength_le Q j b L hQ hjQ hbQ hp.2 ht
    have hP2 : P.card = 2 := by
      have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj.1
      dsimp only [P, Q] at hP hlen ⊢
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
      omega
    have hq0 : 2 - (Q.card : ℤ) + (L.length : ℤ) = 0 := by
      have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj.1
      dsimp only [P, Q] at hP2 ⊢
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
      omega
    have hr := ih Q j b (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht hq0
    have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_hom_unit (A := R) x P a j (2 - (P.card : ℤ)) hP
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ha hj.2.1.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)) rfl hP2
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
    dsimp only [List.casesOn]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_unit_of_heq (A := R) _ _ _ rfl (by omega) hf).trans hr

/-- 定値入力の同じ実切断合成と次数による零・単位の判定。 -/
lemma dgNerveCutProduct_constant_zero {n : ℕ} (x : D)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) (hk0 : 2 - (I.card : ℤ) + (S.card : ℤ) ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
      I a b S hI ha hb hc = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct
  exact dgNerveListCutProduct_constant_zero R D x I a b (S.sort (· ≤ ·)) _ _ hI ha hb
    (Finset.sortedLT_sort S).pairwise
    (fun j hj => hc j ((Finset.mem_sort (· ≤ ·)).mp hj)) hk0
/-- 定値入力の同じ実切断合成と次数による零・単位の判定。 -/
lemma dgNerveCutProduct_constant_unit {n : ℕ} (x : D)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) (hk0 : 2 - (I.card : ℤ) + (S.card : ℤ) = 0) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
      I a b S hI ha hb hc) (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct
  exact dgNerveListCutProduct_constant_unit R D x I a b (S.sort (· ≤ ·)) _ _ hI ha hb
    (Finset.sortedLT_sort S).pairwise
    (fun j hj => hc j ((Finset.mem_sort (· ≤ ·)).mp hj)) hk0
end SerrePositivity.InfinityCategories.Project.DerivedCategories
