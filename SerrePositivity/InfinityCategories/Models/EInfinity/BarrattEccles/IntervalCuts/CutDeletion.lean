module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutValidity
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Deletion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Modules

/-!
模型。文献の定義との比較は後で
# 切断点以外の文字削除と非退化性

概要：Berger–Fresse §2.2.7 の切断と削除の比較に必要な削除後の基底語を構成する。
方針：切断の左右の単射性を削除後へ制限し、隣接する同色がないことを導く。
規約：切断点以外を削除する。全射性は削除色に別の出現があることから得る。
使われ方：出力辺の二端点の境界項を χ の実際の非退化削除項へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非零な辺の切断を持つ語は隣接非退化（BF §2.2.1）。
方針：隣接する同色の二出現の間に切断点が厳密に入ることはできない。
規約：全射性を仮定しない。
使われ方：削除後の切断から削除後の語の非退化性を得る。 -/
lemma nondegenerate_of_edgeNondegenerate {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate u := by
  intro i j hij hu
  have hlt : i < j := by change i.val < j.val; omega
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.repeated_straddles h hlt hu
  have hi := Fin.lt_def.mp hs.1
  have hj := Fin.lt_def.mp hs.2
  omega

/-- 概要：切断点を残す一文字削除は切断の非退化性を保つ（BF §2.2.7）。
方針：削除の順序単射で左右の単射性を制限する。
規約：元の切断点を削除後の位置 q の像で指定する。
使われ方：削除項の実際の辺切断の非零性。 -/
lemma erase_edgeNondegenerate {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (i.succAbove q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff]
  have hm := (Fin.strictMono_succAbove i).monotone
  constructor
  · intro a b ha hb hab
    apply Fin.succAbove_right_injective
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h _ _ (hm ha) (hm hb) hab
  · intro a b ha hb hab
    apply Fin.succAbove_right_injective
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective h _ _ (hm ha) (hm hb) hab

/-- 概要：切断点以外の削除後も元の語は隣接非退化（BF §2.2.7）。
方針：残した切断点の削除後の位置を選び、非零切断から非退化性を得る。
規約：削除後の全射性は別に扱う。
使われ方：χ の削除項の退化判定を除去する。 -/
lemma erase_nondegenerate_of_cut {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (p i : Fin (l + 1)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (hi : i ≠ p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) := by
  obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq hi.symm
  rw [← hq] at h
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nondegenerate_of_edgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_edgeNondegenerate u i q h)

/-- 概要：切断点以外の反復文字の削除は次数を一つ下げた基底語（BF §2.2.7）。
方針：別の同色出現から全射性を得て、切断を残す削除の非退化性を付ける。
規約：元の語の次数は d+1、削除後は d。
使われ方：切断の境界と実際の χ の基底削除項を同じ語で比較する。 -/
def eraseCutBasisWord {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) (p i : Fin (n + (d + 1)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) (hi : i ≠ p)
    (hr : ∃ j, j ≠ i ∧ u.val j = u.val i) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_surjective_iff u.val u.surjective i).mpr hr,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_nondegenerate_of_cut u.val p i h hi⟩

/-- 概要：切断を残す反復色の削除生成元は実際の削除基底元（BF §2.2.7）。
方針：全射・非退化性の証明を持つ削除語に生成元の基底評価を適用する。
規約：任意の可換環。
使われ方：符号付き削除和を退化項なしの基底の和へ移す。 -/
lemma generator_erase_of_cut (A : Type*) [CommRing A] {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (p i : Fin (n + (d + 1))) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) (hi : i ≠ p)
    (hr : ∃ j, j ≠ i ∧ u.val j = u.val i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.eraseCutBasisWord u p i h hi hr)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.eraseCutBasisWord u p i h hi hr)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
