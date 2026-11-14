module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutProductAtDegree
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutSplit
/-!
概要：先頭切断の左右に切断点を追加した実合成を、同じ左右ブロックへ照合する。
方針：元の昇順切断列と区間添字を比較し、実 Hom・実合成の一致を使う。
規約：同じ実 cochain を使う。使われ方：非空切断の境界和の再帰式と全 HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 同じ指定次数の実切断合成と左右ブロックの比較。 -/
lemma dgNerveCutProductAtDegree_insert_after_first {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b i j : Fin (n + 1)) (U : Finset (Fin (n + 1)))
    (hij : i < j) (k p q : ℤ)
    (hk : k = 2 - (I.card : ℤ) + ((insert j (insert i U)).card : ℤ))
    (hp : p = 2 - ((I.filter (· ≤ i)).card : ℤ))
    (hq : q = 2 - ((I.filter (i ≤ ·)).card : ℤ) + ((insert j U).card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ insert j (insert i U), x ∈ I ∧ a < x ∧ x < b)
    (hmin : ∀ x ∈ U, i < x)
    (hP : 2 ≤ (I.filter (· ≤ i)).card)
    (haP : IsLeast ((I.filter (· ≤ i)) : Set (Fin (n + 1))) a)
    (hiP : IsGreatest ((I.filter (· ≤ i)) : Set (Fin (n + 1))) i)
    (hQ : 2 ≤ (I.filter (i ≤ ·)).card)
    (hiQ : IsLeast ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) i)
    (hbQ : IsGreatest ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) b)
    (hcU : ∀ x ∈ insert j U, x ∈ I.filter (i ≤ ·) ∧ i < x ∧ x < b)
    (hpq : p + q = k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s I a b (insert j (insert i U)) k hk hI ha hb hc =
      compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.filter (i ≤ ·)) i b (insert j U)
        q hq hQ hiQ hbQ hcU)
        (s.hom (I.filter (· ≤ i)) a i p hP
          (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
          (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp) hpq := by
  have he : insert j (insert i U) = insert i (insert j U) := Finset.insert_comm _ _ _
  have hk' : k = 2 - (I.card : ℤ) + ((insert i (insert j U)).card : ℤ) := by
    rw [← he]
    exact hk
  have hc' : ∀ x ∈ insert i (insert j U), x ∈ I ∧ a < x ∧ x < b := by
    rw [← he]
    exact hc
  have hmin' : ∀ x ∈ insert j U, i < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hij
    · exact hmin x hx
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree_insert_compose R D s I a b i (insert j U) k p q
    hk' hp hq hI ha hb hc' hmin' hP haP hiP hQ hiQ hbQ hcU hpq
  have hFull : HEq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s I a b (insert j (insert i U)) k hk hI ha hb hc)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s I a b (insert i (insert j U)) k hk' hI ha hb hc') :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s rfl rfl rfl
      (congrArg (fun V : Finset (Fin (n + 1)) => V.sort (· ≤ ·)) he) rfl
  exact eq_of_heq (hFull.trans (heq_of_eq h))
/-- 同じ指定次数の実切断合成と左右ブロックの比較。 -/
lemma dgNerveCutProductAtDegree_insert_before_first {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b i j : Fin (n + 1)) (U : Finset (Fin (n + 1)))
    (hji : j < i) (k p q : ℤ)
    (hk : k = 2 - (I.card : ℤ) + ((insert j (insert i U)).card : ℤ))
    (hp : p = 2 - ((I.filter (· ≤ i)).card : ℤ) + (({j} : Finset (Fin (n + 1))).card : ℤ))
    (hq : q = 2 - ((I.filter (i ≤ ·)).card : ℤ) + (U.card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ insert j (insert i U), x ∈ I ∧ a < x ∧ x < b)
    (hmin : ∀ x ∈ U, i < x)
    (hP : 2 ≤ (I.filter (· ≤ i)).card)
    (haP : IsLeast ((I.filter (· ≤ i)) : Set (Fin (n + 1))) a)
    (hiP : IsGreatest ((I.filter (· ≤ i)) : Set (Fin (n + 1))) i)
    (hQ : 2 ≤ (I.filter (i ≤ ·)).card)
    (hiQ : IsLeast ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) i)
    (hbQ : IsGreatest ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) b)
    (hcJ : ∀ x ∈ ({j} : Finset (Fin (n + 1))), x ∈ I.filter (· ≤ i) ∧ a < x ∧ x < i)
    (hcU : ∀ x ∈ U, x ∈ I.filter (i ≤ ·) ∧ i < x ∧ x < b) (hpq : p + q = k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s I a b (insert j (insert i U)) k hk hI ha hb hc =
      compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.filter (i ≤ ·)) i b U
        q hq hQ hiQ hbQ hcU)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.filter (· ≤ i)) a i {j}
          p hp hP haP hiP hcJ) hpq := by
  have hiU : i ∉ U := fun hx => lt_irrefl i (hmin i hx)
  have hjMin : ∀ x ∈ insert i U, j ≤ x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hji.le
    · exact (lt_trans hji (hmin x hx)).le
  have hjNot : j ∉ insert i U := by
    intro hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact (ne_of_lt hji) hx
    · exact lt_asymm hji (hmin j hx)
  have hsort : (insert j (insert i U)).sort (· ≤ ·) =
      [j] ++ i :: U.sort (· ≤ ·) := by
    rw [Finset.sort_insert (· ≤ ·) hjMin hjNot,
      Finset.sort_insert (· ≤ ·) (fun x hx => (hmin x hx).le) hiU]
    simp only [List.cons_append, List.nil_append]
  have hkList : k = 2 - (I.card : ℤ) + (([j] ++ i :: U.sort (· ≤ ·)).length : ℤ) := by
    rw [← hsort, Finset.length_sort]
    exact hk
  have ho : ([j] ++ i :: U.sort (· ≤ ·)).Pairwise (· < ·) := by
    rw [← hsort]
    exact (Finset.sortedLT_sort _).pairwise
  have hcFull : ∀ x ∈ [j] ++ i :: U.sort (· ≤ ·), x ∈ I ∧ a < x ∧ x < b := by
    intro x hx
    rw [← hsort] at hx
    exact hc x ((Finset.mem_sort (· ≤ ·)).mp hx)
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_split R D s [j] (U.sort (· ≤ ·)) i I a b k p q
    hkList (by simpa only [List.length_singleton, Finset.card_singleton] using hp)
    (by simpa only [Finset.length_sort] using hq) hI ha hb hP haP hiP hQ hiQ hbQ
    ho (by simp) (Finset.sortedLT_sort U).pairwise hcFull
    (fun x hx => hcJ x (by simpa only [Finset.mem_singleton, List.mem_singleton] using hx))
    (fun x hx => hcU x ((Finset.mem_sort (· ≤ ·)).mp hx)) hpq
  have hFull : HEq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s I a b (insert j (insert i U)) k hk hI ha hb hc)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s I a b ([j] ++ i :: U.sort (· ≤ ·)) k hkList hI ha hb
        ho hcFull) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s rfl rfl rfl hsort rfl
  have hAll := hFull.trans (heq_of_eq h)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree, Finset.sort_singleton] using! eq_of_heq hAll
end SerrePositivity.InfinityCategories.Project.DerivedCategories
