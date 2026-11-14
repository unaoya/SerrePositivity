module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutProduct
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveListCutStep
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveListCutHEq
/-!
概要：同じ実切断合成を指定次数で使い、先頭切断の一段の実合成へ展開する。
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
def dgNerveCutProductAtDegree {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (S.card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b) : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a) (s.obj b) k :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s I a b (S.sort (· ≤ ·)) k (by rwa [Finset.length_sort])
    hI ha hb (Finset.sortedLT_sort S).pairwise
    (fun x hx => hc x ((Finset.mem_sort (· ≤ ·)).mp hx))
/-- 同じ指定次数の実切断合成と左右ブロックの比較。 -/
lemma dgNerveCutProductAtDegree_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (S.card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ S, x ∈ I ∧ a < x ∧ x < b) :
    HEq (dgNerveCutProductAtDegree R D s I a b S k hk hI ha hb hc)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D s I a b S hI ha hb hc) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s rfl rfl rfl rfl hk
/-- 同じ指定次数の実切断合成と左右ブロックの比較。 -/
lemma dgNerveCutProductAtDegree_insert_step {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b i : Fin (n + 1)) (U : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + ((insert i U).card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ insert i U, x ∈ I ∧ a < x ∧ x < b)
    (hmin : ∀ x ∈ U, i < x)
    (hkStep : k = 2 - (I.card : ℤ) + ((i :: U.sort (· ≤ ·)).length : ℤ))
    (hoStep : (i :: U.sort (· ≤ ·)).Pairwise (· < ·))
    (hcStep : ∀ x ∈ i :: U.sort (· ≤ ·), x ∈ I ∧ a < x ∧ x < b) :
    dgNerveCutProductAtDegree R D s I a b (insert i U) k hk hI ha hb hc =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutStep R D s I a b i (U.sort (· ≤ ·)) k hkStep ha hb hoStep hcStep := by
  have hiU : i ∉ U := fun hx => lt_irrefl i (hmin i hx)
  have hs : (insert i U).sort (· ≤ ·) = i :: U.sort (· ≤ ·) :=
    Finset.sort_insert (· ≤ ·) (fun x hx => (hmin x hx).le) hiU
  have hFull : HEq (dgNerveCutProductAtDegree R D s I a b (insert i U) k hk hI ha hb hc)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s I a b (i :: U.sort (· ≤ ·)) k hkStep hI ha hb
        hoStep hcStep) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s rfl rfl rfl hs rfl
  exact eq_of_heq (hFull.trans (heq_of_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_cons R D s I a b i (U.sort (· ≤ ·)) k hkStep hI ha hb hoStep hcStep)))
/-- 同じ指定次数の実切断合成と左右ブロックの比較。 -/
lemma dgNerveCutProductAtDegree_insert_compose {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b i : Fin (n + 1)) (U : Finset (Fin (n + 1)))
    (k p q : ℤ) (hk : k = 2 - (I.card : ℤ) + ((insert i U).card : ℤ))
    (hp : p = 2 - ((I.filter (· ≤ i)).card : ℤ))
    (hq : q = 2 - ((I.filter (i ≤ ·)).card : ℤ) + (U.card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ insert i U, x ∈ I ∧ a < x ∧ x < b) (hmin : ∀ x ∈ U, i < x)
    (hP : 2 ≤ (I.filter (· ≤ i)).card)
    (haP : IsLeast ((I.filter (· ≤ i)) : Set (Fin (n + 1))) a)
    (hiP : IsGreatest ((I.filter (· ≤ i)) : Set (Fin (n + 1))) i)
    (hQ : 2 ≤ (I.filter (i ≤ ·)).card)
    (hiQ : IsLeast ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) i)
    (hbQ : IsGreatest ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) b)
    (hcU : ∀ x ∈ U, x ∈ I.filter (i ≤ ·) ∧ i < x ∧ x < b) (hpq : p + q = k) :
    dgNerveCutProductAtDegree R D s I a b (insert i U) k hk hI ha hb hc =
      _root_.SerrePositivity.DifferentialGraded.compose R (dgNerveCutProductAtDegree R D s (I.filter (i ≤ ·)) i b U
        q hq hQ hiQ hbQ hcU)
        (s.hom (I.filter (· ≤ i)) a i p hP
          (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
          (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp) hpq := by
  have hiU : i ∉ U := fun hx => lt_irrefl i (hmin i hx)
  have hkStep : k = 2 - (I.card : ℤ) + ((i :: U.sort (· ≤ ·)).length : ℤ) := by
    rw [List.length_cons, Finset.length_sort]
    rw [Finset.card_insert_of_notMem hiU] at hk
    exact hk
  have hoStep : (i :: U.sort (· ≤ ·)).Pairwise (· < ·) := by
    apply List.pairwise_cons.mpr
    exact ⟨fun x hx => hmin x ((Finset.mem_sort (· ≤ ·)).mp hx),
      (Finset.sortedLT_sort U).pairwise⟩
  have hcStep : ∀ x ∈ i :: U.sort (· ≤ ·), x ∈ I ∧ a < x ∧ x < b := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc _ (Finset.mem_insert_self _ _)
    · exact hc x (Finset.mem_insert_of_mem ((Finset.mem_sort (· ≤ ·)).mp hx))
  rw [dgNerveCutProductAtDegree_insert_step R D s I a b i U k hk hI ha hb hc
    hmin hkStep hoStep hcStep]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutStep
  dsimp only
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl hp.symm ?_ rfl _ _ _ _ ?_ ?_ _ _
  · simpa only [Finset.length_sort] using hq.symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s rfl rfl rfl rfl (by
      simpa only [Finset.length_sort] using hq.symm)
  · exact s.hom_heq_of_indices_degree rfl rfl rfl hp.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
