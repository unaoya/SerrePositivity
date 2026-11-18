module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalSingleton
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletedVertexRows

/-!
模型。文献の定義との比較は後で
# 一文字行の全ての削除符号と頂点境界

概要：Berger–Fresse §1.4.4 の一文字行の削除係数を最終行も含めて計算する。
方針：非最終行は区切り順位、最終行は末尾の隣接重複の符号反転を使う。
規約：元の table の次数は正で、退化出力を捨てない。
使われ方：頂点削除に対応する削除微分の項の符号を確定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：行数 d+2 のリストを先行 d 行と最終二行に分ける（BF §1.4.4）。
方針：drop の先頭を二回取り出す。
規約：最後の二つの getElem の存在は行数から従う。
使われ方：最終一文字行の前の行を指定する。 -/
lemma eq_take_append_last_two {α : Type*} (xs : List α) (d : ℕ) (hl : xs.length = d + 2) :
    xs = xs.take d ++ [xs[d], xs[d + 1]] := by
  have hd : d < xs.length := by omega
  have hd' : d + 1 < xs.length := by omega
  have he : xs.drop (d + 2) = [] := List.drop_eq_nil_iff.mpr (by omega)
  calc
    _ = xs.take d ++ xs.drop d := (List.take_append_drop d xs).symm
    _ = _ := by rw [List.drop_eq_getElem_cons hd, List.drop_eq_getElem_cons hd', he]

/-- 概要：Schedule の長さの証明書から各抽出行の長さを読む（BF §1.4.4）。
方針：写像された行長リストの Option 評価を比較する。
規約：行のリストの添字を Schedule の有限添字で指定する。
使われ方：最後の抽出行が実際に一文字であることを確定する。 -/
lemma picked_length_at {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (picked : List (List (Fin n)))
    (hl : picked.length = d + 1)
    (he : picked.map List.length = List.ofFn (fun j => (r.val j).val)) (i : Fin (d + 1)) :
    (picked[i.val]'(by rw [hl]; exact i.isLt)).length = (r.val i).val := by
  have hi : i.val < picked.length := by rw [hl]; exact i.isLt
  have hg := congrArg (fun xs => xs[i.val]?) he
  rw [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
    List.getElem?_ofFn, dite_eq_left i.isLt] at hg
  exact Option.some.inj hg

/-- 概要：成功 table の最終一文字行の削除符号は最後の頂点境界と一致（BF §1.4.4）。
方針：抽出証明書を最終二行で分け、末尾の隣接重複の削除係数を計算する。
規約：次数は d+1 であり、少なくとも二行を持つ。
使われ方：最終頂点削除に対応する退化 table の項を保持する。 -/
lemma deletionCoefficient_singleton_final {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (hi : (r.val (Fin.last (d + 1))).val = 1)
    (k : Fin out.length) (hk : k.val + 1 = out.length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k =
      (-1 : ℤ) ^ (d + 1) := by
  obtain ⟨picked, he, hs, hc, hn, hl, hlengths⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_of_reduction w r out h
  have hl' : picked.length = d + 2 := by omega
  have hd : d < picked.length := by omega
  have hd' : d + 1 < picked.length := by omega
  have hlast : (picked[d + 1]).length = 1 := by
    have hg := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.picked_length_at r picked hl hlengths (Fin.last (d + 1))
    simpa only [Fin.val_last, hi] using hg
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlast
  have hsplit : picked = picked.take d ++ [picked[d], [a]] := by
    calc
      _ = picked.take d ++ [picked[d], picked[d + 1]] := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.eq_take_append_last_two picked d hl'
      _ = _ := by rw [ha]
  have hr : picked[d] ≠ [] := hn _ (List.getElem_mem hd)
  have hbefore : ∀ row ∈ picked.take d, row ≠ [] := by
    intro row hm
    exact hn row (List.mem_of_mem_take hm)
  have hbc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds (picked.take d ++ [picked[d], [a]]) := by
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds hsplit).mp hc
  have hbs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows (picked.take d ++ [picked[d], [a]]) := by
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows hsplit).mp hs
  have hbe : (picked.take d ++ [picked[d], [a]]).flatten = out := by
    exact (congrArg List.flatten hsplit).symm.trans he
  have hcoeff := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_final_singleton (picked.take d) picked[d] a hr
    hbefore hbc hbs out hbe k hk
  have htake : (picked.take d).length = d := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  simpa only [htake] using hcoeff

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
