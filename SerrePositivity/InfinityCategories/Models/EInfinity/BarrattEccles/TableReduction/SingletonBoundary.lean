module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonSigns

/-!
模型。文献の定義との比較は後で
# 一文字行と頂点境界の値・位置・符号

概要：Berger–Fresse §1.4.4 の一文字行を消す境界項の証明書を与える。
方針：Schedule の削除、出力の削除位置、全ての行の交代符号を組み合わせる。
規約：最終行と退化出力も含む。
使われ方：残りの削除項の相殺後に BE の頂点境界を同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：最後の成分を加えると先行部分和は全体の和になる（BF §1.4.4）。
方針：take と drop の分割を取り、最後の drop が一成分だけであることを使う。
規約：i は自然数で指定した最終位置。
使われ方：最終一文字行より前の出力長を求める。 -/
lemma sum_take_add_last (xs : List ℕ) (i : ℕ) (hi : i + 1 = xs.length) :
    (xs.take i).sum + xs[i] = xs.sum := by
  have hb : i < xs.length := by omega
  have he : xs.drop (i + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
  have hd : xs.drop i = [xs[i]] := by rw [List.drop_eq_getElem_cons hb, he]
  have hs := List.sum_take_add_sum_drop xs i
  simpa only [hd, List.sum_cons, List.sum_nil, Nat.add_zero] using hs

/-- 概要：一文字行の削除係数は全ての行で頂点境界の符号（BF §1.4.4）。
方針：最終行以外を区切りで評価し、最終行では隣接重複を使う。
規約：削除位置は先行行長の総和。
使われ方：table の削除項の係数を余面の符号へ置き換える。 -/
lemma deletionCoefficient_singleton {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (i : Fin (d + 2)) (hi : (r.val i).val = 1) (k : Fin out.length)
    (hk : ((List.ofFn (fun j => (r.val j).val)).take i.val).sum = k.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k =
      (-1 : ℤ) ^ i.val := by
  by_cases hb : i.val < d + 1
  · let j : Fin (d + 1) := ⟨i.val, hb⟩
    have he : j.castSucc = i := Fin.ext rfl
    have hcoeff := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_singleton_nonfinal w r out h j
      (by rw [he]; exact hi) k hk
    exact hcoeff
  · have he : i = Fin.last (d + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
    have hilast : (r.val (Fin.last (d + 1))).val = 1 := by rw [← he]; exact hi
    have hl : i.val + 1 = (List.ofFn (fun j => (r.val j).val)).length := by
      simp only [List.length_ofFn]
      omega
    have hsum := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_take_add_last (List.ofFn (fun j => (r.val j).val)) i.val hl
    have hval : (List.ofFn (fun j => (r.val j).val))[i.val] = 1 := by
      simpa only [List.getElem_ofFn, Fin.eta] using hi
    have htotal : (List.ofFn (fun j => (r.val j).val)).sum = n + (d + 1) := by
      simpa only [List.sum_ofFn] using r.property.2
    have hout := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h
    rw [hval, hk, htotal] at hsum
    have hcoeff := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_singleton_final w r out h hilast k (by omega)
    simpa only [he, Fin.val_last] using hcoeff

/-- 概要：一文字行の削除は値・位置・符号を保って頂点境界へ移る（BF §1.4.4）。
方針：行削除の抽出公式と削除係数を同じ出力分割に適用する。
規約：全ての頂点位置を含み、退化出力も保持する。
使われ方：一般の TR の境界恒等式で頂点境界に残る項を同定する。 -/
lemma singleton_boundary_certificate {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (i : Fin (d + 2)) (hi : (r.val i).val = 1)
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    ∃ (pre : List (Fin n)) (a : Fin n) (post : List (Fin n)),
      out = pre ++ a :: post ∧
      pre.length = ((List.ofFn (fun j => (r.val j).val)).take i.val).sum ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)) [] =
        some (pre ++ post) ∧
      ∃ k : Fin out.length, k.val = pre.length ∧
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k =
          (-1 : ℤ) ^ i.val := by
  obtain ⟨pre, a, post, he, hl, hc⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_deleted_vertex w r i hi out h
  have hb : pre.length < out.length := by rw [he]; simp
  let k : Fin out.length := ⟨pre.length, hb⟩
  refine ⟨pre, a, post, he, hl, hc, k, rfl, ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_singleton w r out h i hi k hl.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
