module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutProductAtDegree
/-!
概要：先頭切断の左右で頂点を削除した実合成を、同じ左右ブロックへ照合する。
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
lemma dgNerveCutProductAtDegree_erase_after_first {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b i j : Fin (n + 1)) (U : Finset (Fin (n + 1)))
    (hij : i < j) (k p q : ℤ)
    (hk : k = 2 - ((I.erase j).card : ℤ) + ((insert i U).card : ℤ))
    (hp : p = 2 - ((I.filter (· ≤ i)).card : ℤ))
    (hq : q = 2 - (((I.filter (i ≤ ·)).erase j).card : ℤ) + (U.card : ℤ))
    (hE : 2 ≤ (I.erase j).card)
    (haE : IsLeast ((I.erase j) : Set (Fin (n + 1))) a)
    (hbE : IsGreatest ((I.erase j) : Set (Fin (n + 1))) b)
    (hcE : ∀ x ∈ insert i U, x ∈ I.erase j ∧ a < x ∧ x < b)
    (hmin : ∀ x ∈ U, i < x)
    (hP : 2 ≤ (I.filter (· ≤ i)).card)
    (haP : IsLeast ((I.filter (· ≤ i)) : Set (Fin (n + 1))) a)
    (hiP : IsGreatest ((I.filter (· ≤ i)) : Set (Fin (n + 1))) i)
    (hQ : 2 ≤ ((I.filter (i ≤ ·)).erase j).card)
    (hiQ : IsLeast (((I.filter (i ≤ ·)).erase j) : Set (Fin (n + 1))) i)
    (hbQ : IsGreatest (((I.filter (i ≤ ·)).erase j) : Set (Fin (n + 1))) b)
    (hcU : ∀ x ∈ U, x ∈ (I.filter (i ≤ ·)).erase j ∧ i < x ∧ x < b)
    (hpq : p + q = k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.erase j) a b (insert i U) k hk hE haE hbE hcE =
      compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s ((I.filter (i ≤ ·)).erase j) i b U
        q hq hQ hiQ hbQ hcU)
        (s.hom (I.filter (· ≤ i)) a i p hP
          (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
          (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp) hpq := by
  have hPn : j ∉ I.filter (· ≤ i) := by
    intro hx
    exact not_le_of_gt hij (Finset.mem_filter.mp hx).2
  have hPe : (I.erase j).filter (· ≤ i) = I.filter (· ≤ i) := by
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem hPn]
  have hQe : (I.erase j).filter (i ≤ ·) = (I.filter (i ≤ ·)).erase j :=
    Finset.filter_erase _ _ _
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree_insert_compose R D s (I.erase j) a b i U k p q
    hk (by rw [hPe]; exact hp) (by rw [hQe]; exact hq) hE haE hbE hcE hmin
    (by rw [hPe]; exact hP) (by rw [hPe]; exact haP) (by rw [hPe]; exact hiP)
    (by rw [hQe]; exact hQ) (by rw [hQe]; exact hiQ) (by rw [hQe]; exact hbQ)
    (by rw [hQe]; exact hcU) hpq
  rw [h]
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl rfl rfl rfl _ _ _ _ ?_ ?_ _ _
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s hQe rfl rfl rfl rfl
  · exact s.hom_heq_of_indices_degree hPe rfl rfl rfl
/-- 同じ指定次数の実切断合成と左右ブロックの比較。 -/
lemma dgNerveCutProductAtDegree_erase_before_first {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b i j : Fin (n + 1)) (U : Finset (Fin (n + 1)))
    (hji : j < i) (k p q : ℤ)
    (hk : k = 2 - ((I.erase j).card : ℤ) + ((insert i U).card : ℤ))
    (hp : p = 2 - (((I.filter (· ≤ i)).erase j).card : ℤ))
    (hq : q = 2 - ((I.filter (i ≤ ·)).card : ℤ) + (U.card : ℤ))
    (hE : 2 ≤ (I.erase j).card)
    (haE : IsLeast ((I.erase j) : Set (Fin (n + 1))) a)
    (hbE : IsGreatest ((I.erase j) : Set (Fin (n + 1))) b)
    (hcE : ∀ x ∈ insert i U, x ∈ I.erase j ∧ a < x ∧ x < b)
    (hmin : ∀ x ∈ U, i < x)
    (hP : 2 ≤ ((I.filter (· ≤ i)).erase j).card)
    (haP : IsLeast (((I.filter (· ≤ i)).erase j) : Set (Fin (n + 1))) a)
    (hiP : IsGreatest (((I.filter (· ≤ i)).erase j) : Set (Fin (n + 1))) i)
    (hQ : 2 ≤ (I.filter (i ≤ ·)).card)
    (hiQ : IsLeast ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) i)
    (hbQ : IsGreatest ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) b)
    (hcU : ∀ x ∈ U, x ∈ I.filter (i ≤ ·) ∧ i < x ∧ x < b)
    (hpq : p + q = k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.erase j) a b (insert i U) k hk hE haE hbE hcE =
      compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.filter (i ≤ ·)) i b U
        q hq hQ hiQ hbQ hcU)
        (s.hom ((I.filter (· ≤ i)).erase j) a i p hP
          (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
          (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp) hpq := by
  have hQn : j ∉ I.filter (i ≤ ·) := by
    intro hx
    exact not_le_of_gt hji (Finset.mem_filter.mp hx).2
  have hPe : (I.erase j).filter (· ≤ i) = (I.filter (· ≤ i)).erase j :=
    Finset.filter_erase _ _ _
  have hQe : (I.erase j).filter (i ≤ ·) = I.filter (i ≤ ·) := by
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem hQn]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree_insert_compose R D s (I.erase j) a b i U k p q
    hk (by rw [hPe]; exact hp) (by rw [hQe]; exact hq) hE haE hbE hcE hmin
    (by rw [hPe]; exact hP) (by rw [hPe]; exact haP) (by rw [hPe]; exact hiP)
    (by rw [hQe]; exact hQ) (by rw [hQe]; exact hiQ) (by rw [hQe]; exact hbQ)
    (by rw [hQe]; exact hcU) hpq
  rw [h]
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl rfl rfl rfl _ _ _ _ ?_ ?_ _ _
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s hQe rfl rfl rfl rfl
  · exact s.hom_heq_of_indices_degree hPe rfl rfl rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
