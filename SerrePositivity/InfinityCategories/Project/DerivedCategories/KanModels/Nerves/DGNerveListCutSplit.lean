module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveCutIntervalAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveListCutLow
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveListCutHEq
/-!
概要：任意の昇順切断列の実合成を、途中の選択点で左右へ分ける。
方針：左切断列に帰納し、同じ区間添字の比較と実合成の結合則を使う。
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
lemma dgNerveListCutProduct_split {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (L M : List (Fin (n + 1))) (j : Fin (n + 1))
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k p q : ℤ)
    (hk : k = 2 - (I.card : ℤ) + ((L ++ j :: M).length : ℤ))
    (hp : p = 2 - ((I.filter (· ≤ j)).card : ℤ) + (L.length : ℤ))
    (hq : q = 2 - ((I.filter (j ≤ ·)).card : ℤ) + (M.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hP : 2 ≤ (I.filter (· ≤ j)).card)
    (haP : IsLeast ((I.filter (· ≤ j)) : Set (Fin (n + 1))) a)
    (hjP : IsGreatest ((I.filter (· ≤ j)) : Set (Fin (n + 1))) j)
    (hQ : 2 ≤ (I.filter (j ≤ ·)).card)
    (hjQ : IsLeast ((I.filter (j ≤ ·)) : Set (Fin (n + 1))) j)
    (hbQ : IsGreatest ((I.filter (j ≤ ·)) : Set (Fin (n + 1))) b)
    (ho : (L ++ j :: M).Pairwise (· < ·))
    (hoL : L.Pairwise (· < ·)) (hoM : M.Pairwise (· < ·))
    (hc : ∀ x ∈ L ++ j :: M, x ∈ I ∧ a < x ∧ x < b)
    (hcL : ∀ x ∈ L, x ∈ I.filter (· ≤ j) ∧ a < x ∧ x < j)
    (hcM : ∀ x ∈ M, x ∈ I.filter (j ≤ ·) ∧ j < x ∧ x < b)
    (hpq : p + q = k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s I a b (L ++ j :: M) k hk hI ha hb ho hc =
      compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s (I.filter (j ≤ ·)) j b M q hq hQ hjQ hbQ hoM hcM)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s (I.filter (· ≤ j)) a j L p hp hP haP hjP hoL hcL) hpq := by
  induction L generalizing I a k p q with
  | nil =>
    simp only [List.nil_append]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_cons]
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutStep
    dsimp only
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_nil R D s _ a j p (by simpa using hp) hP haP hjP]
    apply eq_of_heq
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl (by simpa using hp.symm)
      hq.symm rfl _ _ _ _ ?_ ?_ _ _
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s rfl rfl rfl rfl hq.symm
    · exact s.hom_heq_of_indices_degree rfl rfl rfl (by simpa using hp.symm)
  | cons i L ih =>
    have hi := hc i (by simp)
    have hij : i < j := (hcL i (by simp)).2.2
    have hjI : j ∈ I := (Finset.mem_filter.mp hjP.1).1
    let T := I.filter (i ≤ ·)
    have hiT : IsLeast (T : Set (Fin (n + 1))) i :=
      ⟨Finset.mem_filter.mpr ⟨hi.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
    have hbT : IsGreatest (T : Set (Fin (n + 1))) b :=
      ⟨Finset.mem_filter.mpr ⟨hb.1, hi.2.2.le⟩,
        fun _ hx => hb.2 (Finset.mem_filter.mp hx).1⟩
    have hT : 2 ≤ T.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hi.1 hb.1 hi.2.2
    have hjT : j ∈ T := Finset.mem_filter.mpr ⟨hjI, hij.le⟩
    have hPT : 2 ≤ (T.filter (· ≤ j)).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hiT.1 hjT hij
    have hQT : 2 ≤ (T.filter (j ≤ ·)).card :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hjT hbT.1 (hc j (by simp)).2.2
    have hiPT : IsLeast ((T.filter (· ≤ j)) : Set (Fin (n + 1))) i :=
      ⟨Finset.mem_filter.mpr ⟨hiT.1, hij.le⟩,
        fun _ hx => hiT.2 (Finset.mem_filter.mp hx).1⟩
    have hjPT : IsGreatest ((T.filter (· ≤ j)) : Set (Fin (n + 1))) j :=
      ⟨Finset.mem_filter.mpr ⟨hjT, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
    have hjQT : IsLeast ((T.filter (j ≤ ·)) : Set (Fin (n + 1))) j :=
      ⟨Finset.mem_filter.mpr ⟨hjT, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
    have hbQT : IsGreatest ((T.filter (j ≤ ·)) : Set (Fin (n + 1))) b :=
      ⟨Finset.mem_filter.mpr ⟨hbT.1, (Finset.mem_filter.mp hbQ.1).2⟩,
        fun _ hx => hbT.2 (Finset.mem_filter.mp hx).1⟩
    have hoT := (List.pairwise_cons.mp ho).2
    have hoLT := (List.pairwise_cons.mp hoL).2
    have hcT : ∀ x ∈ L ++ j :: M, x ∈ T ∧ i < x ∧ x < b := by
      intro x hx
      have hxI := hc x (List.mem_cons_of_mem i hx)
      have hix := (List.pairwise_cons.mp ho).1 x hx
      exact ⟨Finset.mem_filter.mpr ⟨hxI.1, hix.le⟩, hix, hxI.2.2⟩
    have hcLT : ∀ x ∈ L, x ∈ T.filter (· ≤ j) ∧ i < x ∧ x < j := by
      intro x hx
      have hxL := hcL x (List.mem_cons_of_mem i hx)
      have hix := (List.pairwise_cons.mp hoL).1 x hx
      exact ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxL.1).1, hix.le⟩, hxL.2.2.le⟩,
        hix, hxL.2.2⟩
    have hcMT : ∀ x ∈ M, x ∈ T.filter (j ≤ ·) ∧ j < x ∧ x < b := by
      intro x hx
      have hxM := hcM x hx
      exact ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxM.1).1,
          (lt_trans hij hxM.2.1).le⟩, hxM.2.1.le⟩, hxM.2⟩
    let pT : ℤ := 2 - ((T.filter (· ≤ j)).card : ℤ) + (L.length : ℤ)
    let kT : ℤ := 2 - (T.card : ℤ) + ((L ++ j :: M).length : ℤ)
    have hqT : q = 2 - ((T.filter (j ≤ ·)).card : ℤ) + (M.length : ℤ) := by
      dsimp only [T]
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInterval_upper_upper I i j hij.le]
      exact hq
    have hpTq : pT + q = kT := by
      have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hjT
      dsimp only [pT, kT]
      simp only [List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
      omega
    have hsplit := ih T i kT pT q rfl rfl hqT hT hiT hbT hPT hiPT hjPT
      hQT hjQT hbQT hoT hoLT hcT hcLT hcMT hpTq
    let f := s.hom (I.filter (· ≤ i)) a i (2 - ((I.filter (· ≤ i)).card : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two ha.1 hi.1 hi.2.1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ha hi.2.1.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hi.1 _) rfl
    let u := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s (T.filter (· ≤ j)) i j L pT rfl
      hPT hiPT hjPT hoLT hcLT
    let v := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s (I.filter (j ≤ ·)) j b M q hq
      hQ hjQ hbQ hoM hcM
    have hV : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s (T.filter (j ≤ ·)) j b M q hqT
        hQT hjQT hbQT hoM hcMT = v := by
      apply eq_of_heq
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInterval_upper_upper I i j hij.le) rfl rfl rfl rfl
    have hfp : (2 - ((I.filter (· ≤ i)).card : ℤ)) + pT = p := by
      have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card (hcL i (by simp)).1
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInterval_lower_lower I i j hij.le,
        ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInterval_lower_upper I i j] at hs
      dsimp only [pT, T]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hp
      omega
    have hfk : (2 - ((I.filter (· ≤ i)).card : ℤ)) + kT = k := by
      omega
    have hleft : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s (I.filter (· ≤ j)) a j (i :: L)
        p hp hP haP hjP hoL hcL = compose R u f hfp := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_cons]
      unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutStep
      dsimp only
      apply eq_of_heq
      refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl ?_ ?_ rfl _ _ _ _ ?_ ?_ _ _
      · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInterval_lower_lower I i j hij.le]
      · dsimp only [pT, T]
        rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInterval_lower_upper I i j]
      · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInterval_lower_upper I i j).symm rfl rfl rfl (by
            dsimp only [pT, T]
            rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInterval_lower_upper I i j])
      · exact s.hom_heq_of_indices_degree
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInterval_lower_lower I i j hij.le) rfl rfl (by
            rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInterval_lower_lower I i j hij.le])
    rw [hleft]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveGradedCompose_assoc R D f u v hfp hpTq hpq hfk]
    simp only [List.cons_append]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_cons]
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutStep
    dsimp only
    change compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s T i b (L ++ j :: M) kT
      rfl hT hiT hbT hoT hcT) f _ = _
    rw [hsplit, hV]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
