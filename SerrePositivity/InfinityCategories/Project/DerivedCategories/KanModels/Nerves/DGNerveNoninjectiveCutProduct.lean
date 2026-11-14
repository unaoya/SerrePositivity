module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutProductPullback
/-!
概要：選択した切断点上で単射でも、全体が潰れる場合の実切断合成は零となる。
方針：左右の切断上の単射性から全体の単射性を回収し、潰れる部分の零を再帰的に伝える。
規約：元の単体データに HA を仮定しない。使われ方：全次元 tensor 候補の退化成分の消滅。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
/-- 単調写像が切断の左右で単射なら、その和集合である元の添字でも単射。 -/
lemma dgNerveCutSplit_injOn {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (j : Fin (m + 1)) (hj : j ∈ I)
    (hP : Set.InjOn α ((I.filter (· ≤ j)) : Set (Fin (m + 1))))
    (hQ : Set.InjOn α ((I.filter (j ≤ ·)) : Set (Fin (m + 1)))) :
    Set.InjOn α (I : Set (Fin (m + 1))) := by
  have aux : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → α x = α y → x = y := by
    intro x hx y hy hxy he
    by_cases hyj : y ≤ j
    · exact hP (Finset.mem_filter.mpr ⟨hx, hxy.trans hyj⟩)
        (Finset.mem_filter.mpr ⟨hy, hyj⟩) he
    by_cases hjx : j ≤ x
    · exact hQ (Finset.mem_filter.mpr ⟨hx, hjx⟩)
        (Finset.mem_filter.mpr ⟨hy, hjx.trans hxy⟩) he
    have hxj : x ≤ j := (lt_of_not_ge hjx).le
    have hjy : j ≤ y := (lt_of_not_ge hyj).le
    have haxj : α x = α j :=
      le_antisymm (α.monotone hxj) ((α.monotone hjy).trans (le_of_eq he.symm))
    have hajy : α j = α y :=
      le_antisymm (α.monotone hjy) ((le_of_eq he.symm).trans (α.monotone hxj))
    exact (hP (Finset.mem_filter.mpr ⟨hx, hxj⟩)
      (Finset.mem_filter.mpr ⟨hj, le_rfl⟩) haxj).trans
      (hQ (Finset.mem_filter.mpr ⟨hj, le_rfl⟩)
        (Finset.mem_filter.mpr ⟨hy, hjy⟩) hajy)
  intro x hx y hy he
  rcases le_total x y with hxy | hyx
  · exact aux x hx y hy hxy he
  · exact (aux y hy x hx hyx he.symm).symm
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 両端が別々に写る非単射成分は、元の引き戻しの生の Hom で零となる。 -/
lemma dgNerveData_pullback_hom_zero {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hab : α a ≠ α b)
    (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1)))) :
    (s.pullback α).hom I a b k hI ha hb hk = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi
  intro h2
  apply hab
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi h2
    (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
/-- 選択した両端・切断列で単射でも、全添字で非単射なら同じ実切断合成は零。 -/
lemma dgNerveListCutProduct_pullback_zero {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (L : List (Fin (m + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (L.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (m + 1))) a)
    (hb : IsGreatest (I : Set (Fin (m + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b)
    (hSel : Set.InjOn α
      ((insert a (insert b L.toFinset) : Finset (Fin (m + 1))) : Set (Fin (m + 1))))
    (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D (s.pullback α) I a b L k hk hI ha hb ho hc = 0 := by
  induction L generalizing I a b k with
  | nil =>
    have hab : a < b := by
      have h := I.min'_lt_max'_of_card (by omega)
      simpa only [← ha.unique (I.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)),
        ← hb.unique (I.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))] using h
    have hne : α a ≠ α b := by
      intro h
      exact (ne_of_lt hab) (hSel (by simp) (by simp) h)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
    dsimp only [List.casesOn]
    exact dgNerveData_pullback_hom_zero R D s α I a b k hI _ _
      (by simpa using hk) hne hi
  | cons j L ih =>
    have hj := hc j (by simp)
    have hp := List.pairwise_cons.mp ho
    let P := I.filter (· ≤ j)
    let Q := I.filter (j ≤ ·)
    have hP : 2 ≤ P.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two ha.1 hj.1 hj.2.1
    have hQ : 2 ≤ Q.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj.1 hb.1 hj.2.2
    by_cases hiP : Set.InjOn α (P : Set (Fin (m + 1)))
    · have hiQ : ¬ Set.InjOn α (Q : Set (Fin (m + 1))) := by
        intro hQinj
        exact hi (dgNerveCutSplit_injOn α I j hj.1 hiP hQinj)
      have hjQ : IsLeast (Q : Set (Fin (m + 1))) j :=
        ⟨Finset.mem_filter.mpr ⟨hj.1, le_rfl⟩, fun _ hz => (Finset.mem_filter.mp hz).2⟩
      have hbQ : IsGreatest (Q : Set (Fin (m + 1))) b :=
        ⟨Finset.mem_filter.mpr ⟨hb.1, hj.2.2.le⟩,
          fun _ hz => hb.2 (Finset.mem_filter.mp hz).1⟩
      have ht : ∀ z ∈ L, z ∈ Q ∧ j < z ∧ z < b := by
        intro z hz
        have hzI := hc z (List.mem_cons_of_mem j hz)
        have hjz := hp.1 z hz
        exact ⟨Finset.mem_filter.mpr ⟨hzI.1, hjz.le⟩, hjz, hzI.2.2⟩
      have hSelQ : Set.InjOn α
          ((insert j (insert b L.toFinset) : Finset (Fin (m + 1))) : Set (Fin (m + 1))) :=
        hSel.mono (by
          intro z hz
          change z ∈ (insert j (insert b L.toFinset) : Finset (Fin (m + 1))) at hz
          change z ∈ (insert a (insert b (j :: L).toFinset) : Finset (Fin (m + 1)))
          simp only [List.toFinset_cons, Finset.mem_insert] at hz ⊢
          aesop)
      have hrec := ih Q j b (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht
        hSelQ hiQ
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
      dsimp only [List.casesOn]
      rw [hrec, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
    · have hne : α a ≠ α j := by
        intro h
        exact (ne_of_lt hj.2.1) (hSel (by simp) (by simp) h)
      have hfirst := dgNerveData_pullback_hom_zero R D s α P a j
        (2 - (P.card : ℤ)) hP
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ha hj.2.1.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)) rfl hne hiP
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
      dsimp only [List.casesOn]
      rw [hfirst, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero]
/-- 有限切断集合の選択点で単射でも、全添字で非単射なら同じ実合成は零。 -/
lemma dgNerveCutProduct_pullback_zero {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (S : Finset (Fin (m + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (m + 1))) a)
    (hb : IsGreatest (I : Set (Fin (m + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b)
    (hSel : Set.InjOn α
      ((insert a (insert b S) : Finset (Fin (m + 1))) : Set (Fin (m + 1))))
    (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D (s.pullback α) I a b S hI ha hb hc = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct
  apply dgNerveListCutProduct_pullback_zero R D s α I a b (S.sort (· ≤ ·))
    _ _ hI ha hb (Finset.sortedLT_sort S).pairwise (by
      intro j hj
      exact hc j ((Finset.mem_sort (· ≤ ·)).mp hj))
  · simpa only [Finset.sort_toFinset] using hSel
  · exact hi
end SerrePositivity.InfinityCategories.Project.DerivedCategories
