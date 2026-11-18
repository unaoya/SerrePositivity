module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionBlocks
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
模型。文献の定義との比較は後で
# 活動位置列の挿入と両向きの交差逆転

概要：Berger–Fresse §2.2.4・§2.2.6 の一活動位置の列による置換を逆転数で比較する。
方針：非交差な二集合の二重和を内部寄与と両向きの交差寄与へ分ける。
規約：二集合の全体が前後に並ぶことを仮定しない。
使われ方：二出現色の最初の位置へ内側活動列を挿入する場合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

/-- 概要：非交差な二集合の逆転数は内部二項と両向きの交差和（BF §2.2.4）。
方針：二つの添字を和集合で分け、逆向き交差の二重和の順を交換する。
規約：位置順には条件を課さない。
使われ方：内側列の前後に外側活動位置がある場合の全逆転数。 -/
lemma positionInversionCount_disjoint_union {n l : ℕ} (u : Fin l → Fin n)
    (s t : Finset (Fin l)) (hd : Disjoint s t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s ∪ t) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s +
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u t +
        ∑ i ∈ s, ∑ j ∈ t, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i j + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u j i) := by
  have hr : (∑ i ∈ t, ∑ j ∈ s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i j) =
      ∑ j ∈ s, ∑ i ∈ t, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i j := Finset.sum_comm
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount
  simp_rw [Finset.sum_union hd]
  simp only [Finset.sum_add_distrib]
  rw [hr]
  omega

/-- 概要：一位置を除く逆転差はその位置との両向きの交差和（BF §2.2.4）。
方針：既存の削除公式の自己対の零項を除き二和をまとめる。
規約：色の単射性は不要。
使われ方：挿入前の外側逆転数の共通交差項。 -/
lemma positionInversionCount_erase_pair {n l : ℕ} (u : Fin l → Fin n)
    (s : Finset (Fin l)) (a : Fin l) (ha : a ∈ s) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.erase a) +
      ∑ i ∈ s.erase a, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a i) := by
  have hr : (∑ i ∈ s.erase a, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i a) =
      ∑ i ∈ s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i a :=
    Finset.sum_erase s (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, lt_self_iff_false,
      false_and, ite_false])
  have hc : (∑ i ∈ s.erase a, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a i) =
      ∑ i ∈ s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a i :=
    Finset.sum_erase s (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, lt_self_iff_false,
      false_and, ite_false])
  rw [Finset.sum_add_distrib, hr, hc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_erase u s a ha]
  omega

/-- 概要：二つの単射活動像の交差対が元の一位置との対に一致すると交差数は活動数倍（BF §2.2.6）。
方針：内部逆転数を像から戻し、交差対の和を内側集合の個数で集約する。
規約：前後の交差を同時に扱い、元の比較位置 a は残り集合に属さなくてよい。
使われ方：二出現色への内側辺作用の全合成逆転数。 -/
lemma positionInversionCount_splice_images {n l n' l' n'' l'' : ℕ}
    (u : Fin l → Fin n) (v : Fin l' → Fin n') (w : Fin l'' → Fin n'')
    (s : Finset (Fin l)) (t : Finset (Fin l')) (a : Fin l) (f : Fin l → Fin l'')
    (g : Fin l' → Fin l'') (hf : Set.InjOn f s) (hg : Set.InjOn g t)
    (hd : Disjoint (s.image f) (t.image g))
    (hfterm : ∀ i ∈ s, ∀ j ∈ s,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm w (f i) (f j) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i j)
    (hgterm : ∀ i ∈ t, ∀ j ∈ t,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm w (g i) (g j) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm v i j)
    (hcross : ∀ i ∈ s, ∀ j ∈ t,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm w (f i) (g j) + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm w (g j) (f i) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount w (s.image f ∪ t.image g) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount v t +
        t.card * ∑ i ∈ s, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a i) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_disjoint_union w _ _ hd,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_image_of_terms u w s f hf hfterm,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_image_of_terms v w t g hg hgterm]
  congr 1
  rw [Finset.sum_image hf]
  calc
    _ = ∑ i ∈ s, t.card * (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_image hg]
      calc
        _ = ∑ _j ∈ t, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a i) :=
          Finset.sum_congr rfl (fun j hj => hcross i hi j hj)
        _ = _ := by rw [Finset.sum_const, smul_eq_mul]
    _ = _ := by rw [← Finset.mul_sum]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
