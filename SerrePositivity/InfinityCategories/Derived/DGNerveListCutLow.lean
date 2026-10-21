module
public import SerrePositivity.InfinityCategories.Derived.DGNerveListCutProduct
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms
/-!
概要：実切断合成の空列・一要素列の計算を、元の同じ Hom 成分へ照合する。
方針：指定次数とその式を保持し、列の先頭で区切る再帰と実成分の次数比較を使う。
規約：入力の Small 性・Hom の平坦性は不要。使われ方：dg nerve の tensor 候補。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 同じ指定次数の実切断合成またはその空・一切断の式。 -/
lemma dgNerveListCutProduct_nil {n : ℕ} (s : SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    dgNerveListCutProduct R D s I a b [] k
      (by simpa only [List.length_nil, Nat.cast_zero, add_zero] using hk)
      hI ha hb (by simp) (by simp) =
      s.hom I a b k hI (ha.unique (Finset.isLeast_min' I (Index.nonempty hI)))
        (hb.unique (Finset.isGreatest_max' I (Index.nonempty hI))) hk := by
  rw [dgNerveListCutProduct]
/-- 同じ指定次数の実切断合成またはその空・一切断の式。 -/
lemma dgNerveListCutProduct_singleton {n : ℕ} (s : SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b j : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + 1)
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    dgNerveListCutProduct R D s I a b [j] k
      (by simpa only [List.length_singleton, Nat.cast_one] using hk) hI ha hb (by simp) (by
      intro k hk
      have : k = j := List.mem_singleton.mp hk
      subst k
      exact ⟨hj, haj, hjb⟩) =
    compose R
      (s.hom (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ))
        (Index.right_two hj hb.1 hjb)
        (Index.right_min hj (Index.nonempty (Index.right_two hj hb.1 hjb)))
        (Index.right_max hb hjb.le (Index.nonempty (Index.right_two hj hb.1 hjb))) rfl)
      (s.hom (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ))
        (Index.left_two ha.1 hj haj)
        (Index.left_min ha haj.le (Index.nonempty (Index.left_two ha.1 hj haj)))
        (Index.left_max hj (Index.nonempty (Index.left_two ha.1 hj haj))) rfl)
      (by have hs := Index.split_card hj; omega) := by
  rw [dgNerveListCutProduct]
  dsimp only [List.casesOn]
  rw [dgNerveListCutProduct]
  dsimp only [List.casesOn]
  apply eq_of_heq
  refine gradedHom_compose_heq (A := R) rfl rfl rfl rfl (by simp) rfl _ _ _ _
    ?_ (HEq.refl _) _ _
  exact s.hom_heq_of_indices_degree rfl rfl rfl (by simp)
end SerrePositivity.InfinityCategories
