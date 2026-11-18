module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletionCases

/-!
模型。文献の定義との比較は後で
# 残余集合に属する非最終行末

概要：Berger–Fresse §1.4.4 の二種類の残余削除を相殺対の添字として扱う。
方針：行末は同じ行の開始位置と次の開始位置の間にあることを使う。
規約：行長 2 以上の行末だけを一文字行の削除位置から分離する。
使われ方：順方向の相手が残余集合に戻ることと行末側の逆構成の入力を保証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：次の行の開始位置は現在の開始位置＋行長（BF §1.4.4）。
方針：部分和の最後の一成分を取り出す。
規約：非最終行を Fin d で指定する。
使われ方：行末の位置が二つの連続する開始位置の間にあることを示す。 -/
lemma scheduleOffset_succ {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i.succ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i.castSucc + (r.val i.castSucc).val := by
  have hb : i.val < (List.ofFn (fun j => (r.val j).val)).length := by
    simp only [List.length_ofFn]; omega
  have he : (List.ofFn (fun j => (r.val j).val))[i.val] = (r.val i.castSucc).val := by
    rw [List.getElem_ofFn]
    exact congrArg (fun j => (r.val j).val) (Fin.ext rfl)
  change ((List.ofFn (fun j => (r.val j).val)).take (i.val + 1)).sum = _
  rw [List.take_succ_eq_append_getElem hb, List.sum_append, he]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  rfl

/-- 概要：長さ 2 以上の非最終行末は一文字行の開始位置ではない（BF §1.4.4）。
方針：他の全行の開始位置を現在行以前と次の行以降に分ける。
規約：出力の値を使わず、長さと指定した行末位置だけを使う。
使われ方：順方向で得た相手の削除位置が残余和に属することを保証する。 -/
lemma scheduleEnd_not_singleton {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d)
    (hi : 1 < (r.val i.castSucc).val) (out : List (Fin n)) (hl : out.length = n + d)
    (k : Fin out.length) (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i = k.val) :
    k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out hl := by
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one r i
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_succ r i
  intro hx
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
  have hval : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r j = k.val := congrArg Fin.val hj
  by_cases hjle : j ≤ i.castSucc
  · have hm := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_strictMono r).monotone hjle
    omega
  · have hjs : i.succ ≤ j := by
      change i.val + 1 ≤ j.val
      have hjgt : i.castSucc < j := lt_of_not_ge hjle
      change i.val < j.val at hjgt
      omega
    have hm := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_strictMono r).monotone hjs
    omega

/-- 概要：一文字行の行末位置は一文字行の削除集合に属する（BF §1.4.4）。
方針：行末と開始位置が一致することを行長の公式で示す。
規約：有限添字の値を比較して集合の像へ戻す。
使われ方：残余の区切り削除の所属行が長さ 2 以上であることを導く。 -/
lemma scheduleEnd_mem_singleton_of_length_one {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d)
    (hi : (r.val i.castSucc).val = 1) (out : List (Fin n)) (hl : out.length = n + d)
    (k : Fin out.length) (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i = k.val) :
    k ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out hl := by
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one r i
  apply Finset.mem_image.mpr
  refine ⟨i.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
  apply Fin.ext
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i.castSucc = k.val
  omega

/-- 概要：残余の区切り削除は長さ 2 以上の非最終行末（BF §1.4.4）。
方針：区切り列から行末の番号を取り出し、一文字行の分岐を排除する。
規約：退化出力も含む。
使われ方：行末側の全残余位置から逆対応を構成する。 -/
lemma residual_caesura_row {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (k : Fin out.length) (hx : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h))
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k) :
    ∃ i : Fin d, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i = k.val ∧ 1 < (r.val i.castSucc).val := by
  obtain ⟨picked, he, hn, hl, hlengths, hrep⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEnds_of_reduction w r out h
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEnds_caesura_iff picked out hrep k).mp hc)
  have hlen : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked).length = d := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions_length, hl, Nat.add_sub_cancel]
  have hb : j.val < d := by have := j.isLt; omega
  let i : Fin d := ⟨j.val, hb⟩
  have hlookup : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)[i.val]? = some k.val := by
    rw [List.getElem?_eq_getElem j.isLt]
    exact congrArg some hj
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEnds_eq_scheduleEnds r picked hn hl hlengths i
  have hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i = k.val := Option.some.inj (ht.symm.trans hlookup)
  refine ⟨i, hk, ?_⟩
  have hp := r.property.1 i.castSucc
  by_contra hi
  have hone : (r.val i.castSucc).val = 1 := by omega
  exact hx (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_mem_singleton_of_length_one r i hone out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h) k hk)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
