module
public import SerrePositivity.InfinityCategories.Derived.DGNerveListCutLow
public import Mathlib.Data.Finset.Sort
/-!
概要：実内部点集合を昇順列へ移し、同じ全次元の切断合成 cochain と低次式を得る。
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
def dgNerveCutProduct {n : ℕ} (s : SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) :
    GradedHom R (s.obj a) (s.obj b) (2 - (I.card : ℤ) + (S.card : ℤ)) :=
  dgNerveListCutProduct R D s I a b (S.sort (· ≤ ·))
    (2 - (I.card : ℤ) + (S.card : ℤ)) (by rw [Finset.length_sort]) hI ha hb
    (Finset.sortedLT_sort S).pairwise (fun j hj => hc j ((Finset.mem_sort (· ≤ ·)).mp hj))
/-- 同じ指定次数の実切断合成またはその空・一切断の式。 -/
lemma dgNerveCutProduct_empty {n : ℕ} (s : SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    dgNerveCutProduct R D s I a b ∅ hI ha hb (by simp) =
      s.hom I a b _ hI (ha.unique (Finset.isLeast_min' I (Index.nonempty hI)))
        (hb.unique (Finset.isGreatest_max' I (Index.nonempty hI))) (by simp) := by
  have h := dgNerveListCutProduct_nil R D s I a b
    (2 - (I.card : ℤ) + ((∅ : Finset (Fin (n + 1))).card : ℤ)) (by simp) hI ha hb
  simpa only [dgNerveCutProduct, Finset.sort_empty] using! h
/-- 同じ指定次数の実切断合成またはその空・一切断の式。 -/
lemma dgNerveCutProduct_singleton {n : ℕ} (s : SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b j : Fin (n + 1))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    dgNerveCutProduct R D s I a b {j} hI ha hb (by
      intro k hk
      have : k = j := Finset.mem_singleton.mp hk
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
      (by have hc := Index.split_card hj; simp only [Finset.card_singleton]; omega) := by
  have h := dgNerveListCutProduct_singleton R D s I a b j
    (2 - (I.card : ℤ) + (({j} : Finset (Fin (n + 1))).card : ℤ)) (by simp)
    hI ha hb hj haj hjb
  simpa only [dgNerveCutProduct, Finset.sort_singleton] using! h
end SerrePositivity.InfinityCategories
