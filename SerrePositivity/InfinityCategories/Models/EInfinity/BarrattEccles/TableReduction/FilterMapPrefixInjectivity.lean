module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapSelection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapAvailable
public import Mathlib.Data.List.Nodup

/-!
模型。文献の定義との比較は後で
# 末尾を保持する部分射影から先頭選択長を復元する

概要：Berger–Fresse §1.5.7–9 の空語合成で射影した選択語から元の行長を戻す。
方針：残った末尾の文字を相手の先頭部分に戻し、非重複性で元の位置を一致させる。
規約：行は非重複、射影は some の部分で単射、比較する両末尾は残る。
使われ方：同じ削除出力を持つ成功表の非最終行長を揃える。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：保持される先頭部分の末尾は同じ射影を持つ相手の先頭長以下（BF §1.5.7–9）。
方針：末尾の射影値の相手側の所属を部分単射で元に戻し、行の非重複性を使う。
規約：相手の末尾に条件を課さない。
使われ方：両方向の長さ不等式から元の行長の一意性を得る。 -/
lemma take_length_le_of_filterMap_eq {α β : Type*}
    (f : α → Option β) (hf : ∀ a a' b, f a = some b → f a' = some b → a = a')
    (xs : List α) (hn : xs.Nodup) (r s : ℕ) (hr : 0 < r) (hb : r ≤ xs.length)
    (he : (xs.take r).filterMap f = (xs.take s).filterMap f)
    (hlast : ∃ a b, (xs.take r).getLast? = some a ∧ f a = some b) : r ≤ s := by
  obtain ⟨a, b, ha, hf'⟩ := hlast
  have hi : r - 1 < xs.length := by omega
  have hsplit : xs.take r = xs.take (r - 1) ++ [xs[r - 1]] := by
    have hh := List.take_append_getElem hi
    have hr' : r - 1 + 1 = r := by omega
    simpa only [hr'] using hh.symm
  have hva : xs[r - 1] = a := by
    rw [hsplit, List.getLast?_append] at ha
    simpa only [List.getLast?_singleton, Option.some_or, Option.some.injEq] using ha
  have hm : b ∈ (xs.take s).filterMap f := by
    rw [← he]
    exact List.mem_filterMap.mpr ⟨a, List.mem_of_mem_getLast? ha, hf'⟩
  obtain ⟨a', ham, haf⟩ := List.mem_filterMap.mp hm
  have he' : a' = a := hf a' a b haf hf'
  rw [he'] at ham
  obtain ⟨j, hj, hjv⟩ := List.mem_take_iff_getElem.mp ham
  have hj' : j < xs.length := (Nat.lt_min.mp hj).2
  have hindex : j = r - 1 := hn.getElem_inj_iff.mp (hjv.trans hva.symm)
  have hjs : j < s := (Nat.lt_min.mp hj).1
  omega

/-- 概要：両末尾が残る先頭部分は同じ部分射影から長さが一意（BF §1.5.7–9）。
方針：保持末尾の位置による不等式を両方向に適用する。
規約：空選択は対象外。
使われ方：同じ射影行を持つ二つの成功表の非最終選択長を揃える。 -/
lemma take_length_eq_of_filterMap_eq {α β : Type*}
    (f : α → Option β) (hf : ∀ a a' b, f a = some b → f a' = some b → a = a')
    (xs : List α) (hn : xs.Nodup) (r s : ℕ)
    (hr : 0 < r) (hs : 0 < s) (hrb : r ≤ xs.length) (hsb : s ≤ xs.length)
    (he : (xs.take r).filterMap f = (xs.take s).filterMap f)
    (hleft : ∃ a b, (xs.take r).getLast? = some a ∧ f a = some b)
    (hright : ∃ a b, (xs.take s).getLast? = some a ∧ f a = some b) : r = s :=
  Nat.le_antisymm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.take_length_le_of_filterMap_eq f hf xs hn r s hr hrb he hleft)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.take_length_le_of_filterMap_eq f hf xs hn s r hs hsb he.symm hright)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
