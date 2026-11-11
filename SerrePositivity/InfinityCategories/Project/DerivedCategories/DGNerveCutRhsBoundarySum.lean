module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutBoundaryFirstSum
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveListCutRhsHEq
/-!
概要：全切断の再帰的 HA 右辺と実微分を、削除・追加の同じ符号付き和へ同定する。
方針：先頭切断の実 cochain 比較と零拡張した有限和、切断集合への強帰納法を使う。
規約：全次元の同じ実成分を保つ。使われ方：tensor 候補の全 HA の有限和の相殺。
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
/-- 元の実切断合成の境界項と符号付き全和の照合。 -/
lemma dgNerveCutRhs_eq_boundarySum {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRhs R D s I a b S hI ha hb hc =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundarySum R D s I a b S (2 - (I.card : ℤ) + (S.card : ℤ))
        rfl ha hb hc := by
  induction S using Finset.strongInduction generalizing I a b with
  | H S ih =>
    by_cases hS : S = ∅
    · subst S
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRhs_empty_eq_boundarySum R D s I a b hI ha hb
    · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
      let i := S.min' hne
      let U := S.erase i
      have hiS : i ∈ S := Finset.min'_mem S hne
      have hiU : i ∉ U := Finset.notMem_erase _ _
      have he : insert i U = S := Finset.insert_erase hiS
      have hUS : U ⊂ S := Finset.erase_ssubset hiS
      have hmin : ∀ x ∈ U, i < x := by
        intro x hx
        have hxE := Finset.mem_erase.mp hx
        exact lt_of_le_of_ne (S.min'_le x hxE.2) (Ne.symm hxE.1)
      have hc' : ∀ x ∈ insert i U, x ∈ I ∧ a < x ∧ x < b := by
        rw [he]
        exact hc
      have hi := hc i hiS
      have hP : 2 ≤ (I.filter (· ≤ i)).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two ha.1 hi.1 hi.2.1
      have hQ : 2 ≤ (I.filter (i ≤ ·)).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hi.1 hb.1 hi.2.2
      have haP : IsLeast ((I.filter (· ≤ i)) : Set (Fin (n + 1))) a :=
        ⟨Finset.mem_filter.mpr ⟨ha.1, hi.2.1.le⟩,
          fun _ hx => ha.2 (Finset.mem_filter.mp hx).1⟩
      have hiP : IsGreatest ((I.filter (· ≤ i)) : Set (Fin (n + 1))) i :=
        ⟨Finset.mem_filter.mpr ⟨hi.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
      have hiQ : IsLeast ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) i :=
        ⟨Finset.mem_filter.mpr ⟨hi.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
      have hbQ : IsGreatest ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) b :=
        ⟨Finset.mem_filter.mpr ⟨hb.1, hi.2.2.le⟩,
          fun _ hx => hb.2 (Finset.mem_filter.mp hx).1⟩
      have hcU : ∀ x ∈ U, x ∈ I.filter (i ≤ ·) ∧ i < x ∧ x < b := by
        intro x hx
        have hxI := hc x (Finset.mem_erase.mp hx).2
        exact ⟨Finset.mem_filter.mpr ⟨hxI.1, (hmin x hx).le⟩, hmin x hx, hxI.2.2⟩
      let k : ℤ := 2 - (I.card : ℤ) + ((insert i U).card : ℤ)
      let p : ℤ := 2 - ((I.filter (· ≤ i)).card : ℤ)
      let q : ℤ := 2 - ((I.filter (i ≤ ·)).card : ℤ) + (U.card : ℤ)
      have hsum : p + q = k := by
        have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hi.1
        dsimp only [p, q, k]
        rw [Finset.card_insert_of_notMem hiU]
        push_cast
        omega
      have hRec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundarySum_first R D s I a b i U k p q rfl rfl rfl
        hI ha hb hc' hmin hP haP hiP hQ hiQ hbQ hcU hsum
      have hIH := ih U hUS (I.filter (i ≤ ·)) i b hQ hiQ hbQ hcU
      suffices hGoal : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRhs R D s I a b (insert i U) hI ha hb hc' =
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundarySum R D s I a b (insert i U) k rfl ha hb hc' by
        have hAll : ∀ hc0 : ∀ x ∈ insert i U, x ∈ I ∧ a < x ∧ x < b,
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRhs R D s I a b (insert i U) hI ha hb hc0 =
              _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundarySum R D s I a b (insert i U)
                (2 - (I.card : ℤ) + ((insert i U).card : ℤ)) rfl ha hb hc0 := fun _ => hGoal
        exact (he ▸ hAll) hc
      rw [hRec, ← hIH]
      have hsort : (insert i U).sort (· ≤ ·) = i :: U.sort (· ≤ ·) :=
        Finset.sort_insert (· ≤ ·) (fun x hx => (hmin x hx).le) hiU
      have hkStep : k = 2 - (I.card : ℤ) + ((i :: U.sort (· ≤ ·)).length : ℤ) := by
        dsimp only [k]
        rw [List.length_cons, Finset.length_sort, Finset.card_insert_of_notMem hiU]
      have hoStep : (i :: U.sort (· ≤ ·)).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun x hx => hmin x ((Finset.mem_sort (· ≤ ·)).mp hx),
          (Finset.sortedLT_sort U).pairwise⟩
      have hcStep : ∀ x ∈ i :: U.sort (· ≤ ·), x ∈ I ∧ a < x ∧ x < b := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hc' _ (Finset.mem_insert_self _ _)
        · exact hc' x (Finset.mem_insert_of_mem ((Finset.mem_sort (· ≤ ·)).mp hx))
      have hFull : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRhs R D s I a b (insert i U) hI ha hb hc' =
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutRhs R D s I a b (i :: U.sort (· ≤ ·)) k hkStep hI ha hb
            hoStep hcStep :=
        eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutRhs_heq R D s rfl rfl rfl hsort rfl)
      rw [hFull, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutRhs]
      dsimp only [List.casesOn]
      simp only [Finset.length_sort, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRhs, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree, p, q]
      refine congrArg₂ (· + ·) ?_ ?_
      · apply eq_of_heq
        refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl rfl
          (by rw [Finset.length_sort]) rfl _ _ _ _ ?_ (HEq.refl _) _ _
        exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutRhs_heq R D s rfl rfl rfl rfl (by rw [Finset.length_sort])
      · congr 1
        apply eq_of_heq
        refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl rfl
          (by rw [Finset.length_sort]) rfl _ _ _ _ ?_ (HEq.refl _) _ _
        exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s rfl rfl rfl rfl (by rw [Finset.length_sort])
/-- 元の実切断合成の境界項と符号付き全和の照合。 -/
lemma dgNerveCutProduct_differential_eq_boundarySum {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D s.toSimplexData I a b S hI ha hb hc) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundarySum R D s.toSimplexData I a b S
        (2 - (I.card : ℤ) + (S.card : ℤ)) rfl ha hb hc := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct_differential_eq_rhs, dgNerveCutRhs_eq_boundarySum]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
