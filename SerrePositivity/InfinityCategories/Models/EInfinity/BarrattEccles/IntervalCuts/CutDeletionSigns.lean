module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.DeletedActivePositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.RepeatSigns

/-!
模型。文献の定義との比較は後で
# 切断を残す文字削除の実際の符号一致

概要：Berger–Fresse §2.2.7 の非零切断を残す左右の反復文字削除で係数の一致を証明する。
方針：削除後の活動集合を元の活動集合の一位置削除へ同定し、有限逆転数の符号公式を使う。
規約：右辺は実際の削除語の切断符号。退化する元切断からの項は別に扱う。
使われ方：テンソルの二端点の境界項を χ の削除項の符号付き値へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：実際の削除語の切断符号は元の活動集合から一色を除いた交換符号（BF §2.2.7）。
方針：削除後の活動集合の順序単射による像と逆転数の自然性を使う。
規約：同色の活動位置 a は、実際の削除位置 i と異なってもよい。
使われ方：左右二出現のどちらを削除しても同じ残りの交換指数へ戻す。 -/
lemma edgeSign_erase_eq_removed {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (i.succAbove q))
    (a : Fin (l + 1)) (ha : a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q)) (hua : u a = u i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q =
      (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q)).erase a) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_edgeNondegenerate u i q h)]
  calc
    _ = (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q).image i.succAbove) := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_image u i.succAbove (Fin.strictMono_succAbove i)]
      rfl
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_erase_image_eq_erase u i q h a ha hua]

/-- 概要：最初の反復出現の削除係数と削除語の符号は終点境界の係数に一致（BF §2.2.7）。
方針：元の区切りを一つ除く境界符号公式へ、削除語の実際の切断符号を代入する。
規約：元の切断が非零で、切断点を残す。
使われ方：左出現削除の符号付き項と辺の終点境界項の比較。 -/
lemma edgeSign_erase_left_boundary {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val (i.succAbove q)) (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val (i.succAbove q) * (-1 : ℤ) ^
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < u.val i),
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u (i.succAbove q) k)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val i * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i) q := by
  have ha : i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val (i.succAbove q) :=
    Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_eq_removed u.val i q h i ha rfl]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_caesura_boundary u (i.succAbove q) i h hi

/-- 概要：最後の反復出現の削除係数と削除語の符号は始点境界の係数に一致（BF §2.2.7）。
方針：同色の前の活動位置を除く符号と、二つの削除係数の反対性を使う。
規約：a は前、i は後の同色出現で、実際に i を削除する。
使われ方：右出現削除の符号付き項と辺の始点境界項の比較。 -/
lemma edgeSign_erase_right_boundary {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (i a : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val (i.succAbove q)) (hai : a < i) (hua : u.val a = u.val i) :
    -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val (i.succAbove q) * (-1 : ℤ) ^
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < u.val a),
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u (i.succAbove q) k))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val i * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i) q := by
  have ha : a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val (i.succAbove q) :=
    Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨i, hai, hua.symm⟩⟩))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_eq_removed u.val i q h a ha hua]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_final_boundary u (i.succAbove q) a i h hai hua

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
