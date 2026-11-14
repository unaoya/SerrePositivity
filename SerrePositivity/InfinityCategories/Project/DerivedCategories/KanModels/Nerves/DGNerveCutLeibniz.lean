module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveListCutLow
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutProduct
/-!
概要：全次元の実切断合成の微分を、同じブロックの微分および HA 右辺へ再帰的に展開する。
方針：通常順合成の Leibniz 則で列に帰納し、元の実単体の HA を各ブロックに適用する。
規約：原始元や微分式を追加仮定しない。使われ方：符号付き全切断和の高次 HA の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 元のブロックの実微分だけを使う、同じ切断合成の再帰的 Leibniz 境界。 -/
def dgNerveListCutBoundary {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (L : List (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (L.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) (k + 1) := by
  cases L with
  | nil =>
    exact _root_.SerrePositivity.DifferentialGraded.differential R (s.hom I a b k hI
      (ha.unique (Finset.isLeast_min' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)))
      (hb.unique (Finset.isGreatest_max' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)))
        (by simpa only [List.length_nil, Nat.cast_zero, add_zero] using hk))
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
    let rest := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s Q j b L
      (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht
    let dRest := dgNerveListCutBoundary s Q j b L
      (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht
    exact _root_.SerrePositivity.DifferentialGraded.compose R dRest first (by
      have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj.1
      dsimp only [P, Q]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
      omega) +
      (2 - (Q.card : ℤ) + (L.length : ℤ)).negOnePow •
        _root_.SerrePositivity.DifferentialGraded.compose R rest (_root_.SerrePositivity.DifferentialGraded.differential R first) (by
          have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj.1
          dsimp only [P, Q]
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
          omega)
termination_by L.length
/-- 指定次数の同じ実切断合成の微分は、再帰的 Leibniz 境界に一致する。 -/
lemma dgNerveListCutProduct_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (L : List (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (L.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s I a b L k hk hI ha hb ho hc) =
      dgNerveListCutBoundary R D s I a b L k hk hI ha hb ho hc := by
  induction L generalizing I a b k with
  | nil => rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct, dgNerveListCutBoundary]
  | cons j L ih =>
    have hj := hc j (by simp)
    have hp := List.pairwise_cons.mp ho
    let Q := I.filter (j ≤ ·)
    have hQ : 2 ≤ Q.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj.1 hb.1 hj.2.2
    have hjQ : IsLeast (Q : Set (Fin (n + 1))) j :=
      ⟨Finset.mem_filter.mpr ⟨hj.1, le_rfl⟩, fun _ hz => (Finset.mem_filter.mp hz).2⟩
    have hbQ : IsGreatest (Q : Set (Fin (n + 1))) b :=
      ⟨Finset.mem_filter.mpr ⟨hb.1, hj.2.2.le⟩,
        fun _ hz => hb.2 (Finset.mem_filter.mp hz).1⟩
    have ht : ∀ z ∈ L, z ∈ Q ∧ j < z ∧ z < b := by
      intro z hz
      have hzI := hc z (List.mem_cons_of_mem j hz)
      have hjz := hp.1 z hz
      exact ⟨Finset.mem_filter.mpr ⟨hzI.1, hjz.le⟩, hjz, hzI.2.2⟩
    have hrec := ih Q j b (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct, dgNerveListCutBoundary]
    dsimp only [List.casesOn]
    rw [_root_.SerrePositivity.DifferentialGraded.differential_compose, hrec]
/-- 元の各ブロックの HA 右辺を代入した、同じ切断合成の再帰的境界。 -/
def dgNerveListCutRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (L : List (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (L.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) (k + 1) := by
  cases L with
  | nil =>
    exact s.rhs I a b k hI
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
    let rest := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s Q j b L
      (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht
    let dRest := dgNerveListCutRhs s Q j b L
      (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht
    let firstRhs := s.rhs P a j (2 - (P.card : ℤ)) hP
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ha hj.2.1.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)) rfl
    exact _root_.SerrePositivity.DifferentialGraded.compose R dRest first (by
      have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj.1
      dsimp only [P, Q]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
      omega) +
      (2 - (Q.card : ℤ) + (L.length : ℤ)).negOnePow •
        _root_.SerrePositivity.DifferentialGraded.compose R rest firstRhs (by
          have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj.1
          dsimp only [P, Q]
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hk
          omega)
termination_by L.length
/-- 元の入力が実単体なら、ブロックの実微分を同じ HA 右辺に置き換えられる。 -/
lemma dgNerveListCutBoundary_eq_rhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (L : List (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (L.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) :
    dgNerveListCutBoundary R D s.toSimplexData I a b L k hk hI ha hb ho hc =
      dgNerveListCutRhs R D s.toSimplexData I a b L k hk hI ha hb ho hc := by
  induction L generalizing I a b k with
  | nil =>
    rw [dgNerveListCutBoundary, dgNerveListCutRhs]
    dsimp only [List.casesOn]
    exact s.equation I a b k hI _ _ _
  | cons j L ih =>
    have hj := hc j (by simp)
    have hp := List.pairwise_cons.mp ho
    let Q := I.filter (j ≤ ·)
    have hQ : 2 ≤ Q.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj.1 hb.1 hj.2.2
    have hjQ : IsLeast (Q : Set (Fin (n + 1))) j :=
      ⟨Finset.mem_filter.mpr ⟨hj.1, le_rfl⟩, fun _ hz => (Finset.mem_filter.mp hz).2⟩
    have hbQ : IsGreatest (Q : Set (Fin (n + 1))) b :=
      ⟨Finset.mem_filter.mpr ⟨hb.1, hj.2.2.le⟩,
        fun _ hz => hb.2 (Finset.mem_filter.mp hz).1⟩
    have ht : ∀ z ∈ L, z ∈ Q ∧ j < z ∧ z < b := by
      intro z hz
      have hzI := hc z (List.mem_cons_of_mem j hz)
      have hjz := hp.1 z hz
      exact ⟨Finset.mem_filter.mpr ⟨hzI.1, hjz.le⟩, hjz, hzI.2.2⟩
    have hrec := ih Q j b (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht
    rw [dgNerveListCutBoundary, dgNerveListCutRhs]
    dsimp only [List.casesOn]
    rw [hrec, s.equation]
/-- 実単体の同じ切断合成の微分は、各ブロックの HA 右辺の再帰式に一致する。 -/
lemma dgNerveListCutProduct_differential_eq_rhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (L : List (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (L.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s.toSimplexData I a b L k hk hI ha hb ho hc) =
      dgNerveListCutRhs R D s.toSimplexData I a b L k hk hI ha hb ho hc :=
  (dgNerveListCutProduct_differential R D s.toSimplexData I a b L k hk hI ha hb ho hc).trans
    (dgNerveListCutBoundary_eq_rhs R D s I a b L k hk hI ha hb ho hc)
/-- 有限切断集合による、同じ合成の再帰的 Leibniz 境界。 -/
def dgNerveCutBoundary {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) (2 - (I.card : ℤ) + (S.card : ℤ) + 1) :=
  dgNerveListCutBoundary R D s I a b (S.sort (· ≤ ·))
    (2 - (I.card : ℤ) + (S.card : ℤ)) (by rw [Finset.length_sort]) hI ha hb
    (Finset.sortedLT_sort S).pairwise (fun j hj => hc j ((Finset.mem_sort (· ≤ ·)).mp hj))
/-- 有限切断集合による、同じブロックの HA 右辺からなる再帰的境界。 -/
def dgNerveCutRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) (2 - (I.card : ℤ) + (S.card : ℤ) + 1) :=
  dgNerveListCutRhs R D s I a b (S.sort (· ≤ ·))
    (2 - (I.card : ℤ) + (S.card : ℤ)) (by rw [Finset.length_sort]) hI ha hb
    (Finset.sortedLT_sort S).pairwise (fun j hj => hc j ((Finset.mem_sort (· ≤ ·)).mp hj))
/-- 有限切断集合の同じ実合成の微分は、再帰的 Leibniz 境界に一致する。 -/
lemma dgNerveCutProduct_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D s I a b S hI ha hb hc) =
      dgNerveCutBoundary R D s I a b S hI ha hb hc :=
  dgNerveListCutProduct_differential R D s I a b (S.sort (· ≤ ·))
    _ _ hI ha hb (Finset.sortedLT_sort S).pairwise _
/-- 実単体の有限切断合成の微分は、同じブロックの HA 右辺の再帰式に一致する。 -/
lemma dgNerveCutProduct_differential_eq_rhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D s.toSimplexData I a b S hI ha hb hc) =
      dgNerveCutRhs R D s.toSimplexData I a b S hI ha hb hc :=
  dgNerveListCutProduct_differential_eq_rhs R D s I a b (S.sort (· ≤ ·))
    _ _ hI ha hb (Finset.sortedLT_sort S).pairwise _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
