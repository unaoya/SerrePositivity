module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.BlockCoordinates

/-!
模型。文献の定義との比較は後で
# 挿入値の最終出現と直前出現の位置

概要：Berger–Fresse §1.4.4 の逆抽出の語の形から最終出現削除の位置を同定する。
方針：値のない中間語と後続語を用い、二つの指定出現の間と後を排除する。
規約：全射性・非退化性を仮定しない。
使われ方：逆 Schedule の新しい挿入位置と短縮行末を符号の定義へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：挿入位置の出力値は挿入した値（BF §1.4.4）。
方針：長さ 1 のブロックとして位置を評価する。
規約：位置は先行語の長さ。
使われ方：逆抽出の二つの同値の出現の値を比較する。 -/
lemma value_at_insert {n : ℕ} (out pre post : List (Fin n)) (a : Fin n)
    (he : out = pre ++ a :: post) (k : Fin out.length) (hk : k.val = pre.length) :
    out[k.val] = a := by
  have hv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position out pre [a] post he k ⟨0, by simp⟩
    (by simpa only [Nat.add_zero] using hk)
  exact hv

/-- 概要：先行語の後の位置の値は後続語に属する（BF §1.4.4）。
方針：先行長を引いた行内添字で評価する。
規約：出力の長さの証明項を保持する。
使われ方：挿入位置より後に同じ値がないことを示す。 -/
lemma getElem_mem_suffix {α : Type*} (out pre post : List α) (he : out = pre ++ post)
    (j : Fin out.length) (hj : pre.length ≤ j.val) : out[j.val] ∈ post := by
  have hl := congrArg List.length he
  simp only [List.length_append] at hl
  have hb : j.val - pre.length < post.length := by have := j.isLt; omega
  have hv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position out pre post []
    (by simpa only [List.append_nil] using he) j ⟨j.val - pre.length, hb⟩ (by
      change j.val = pre.length + (j.val - pre.length)
      omega)
  exact hv.symm ▸ List.getElem_mem hb

/-- 概要：後続語に挿入値がなければ挿入位置は最終出現（BF §1.4.4）。
方針：それより後の位置を後続語の所属へ移す。
規約：同じ値が前に現れることは許す。
使われ方：逆 Schedule の挿入項が最終出現削除であることを保証する。 -/
lemma not_caesura_at_insert {n : ℕ} (out pre post : List (Fin n)) (a : Fin n)
    (he : out = pre ++ a :: post) (ha : a ∉ post)
    (k : Fin out.length) (hk : k.val = pre.length) :
    ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k := by
  rintro ⟨j, hj, hv⟩
  have hs : out = (pre ++ [a]) ++ post := by
    simpa only [List.append_assoc, List.singleton_append] using he
  have hbound : (pre ++ [a]).length ≤ j.val := by
    simp only [List.length_append, List.length_singleton]
    change k.val < j.val at hj
    omega
  have hmem := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_mem_suffix out (pre ++ [a]) post hs j hbound
  have hvalue := hv.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.value_at_insert out pre post a he k hk)
  exact ha (hvalue ▸ hmem)

/-- 概要：値のない中間語を挟んだ二つの出現では前の指定位置が直前出現（BF §1.4.4）。
方針：中間位置の全ての同値の出現を中間語の不出現で排除する。
規約：先行語には同じ値がいくつ現れていてもよい。
使われ方：逆抽出の直前出現を短縮行末と厳密に同定する。 -/
lemma previousOccurrence_double_insert {n : ℕ} (out pre middle post : List (Fin n)) (a : Fin n)
    (he : out = pre ++ a :: (middle ++ a :: post)) (ha : a ∉ middle)
    (p k : Fin out.length) (hp : p.val = pre.length)
    (hk : k.val = pre.length + 1 + middle.length) :
    ∃ h : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty,
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' h = p := by
  have hvp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.value_at_insert out pre (middle ++ a :: post) a he p hp
  have hs : out = ((pre ++ [a]) ++ middle) ++ a :: post := by
    simpa only [List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append] using he
  have hvk := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.value_at_insert out ((pre ++ [a]) ++ middle) post a hs k (by
    simpa only [List.length_append, List.length_singleton] using hk)
  have hpmem : p ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by change p.val < k.val; omega, hvp.trans hvk.symm⟩
  let hnonempty : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty :=
    ⟨p, hpmem⟩
  refine ⟨hnonempty, le_antisymm ?_ (Finset.le_max' _ p hpmem)⟩
  apply Finset.max'_le
  intro j hj
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  by_contra hle
  have hjlo : (pre ++ [a]).length ≤ j.val := by
    simp only [List.length_append, List.length_singleton]
    have hjgt : p < j := lt_of_not_ge hle
    change p.val < j.val at hjgt
    omega
  have hjhi : j.val < pre.length + 1 + middle.length := by
    have hjk : j.val < k.val := hj.1
    omega
  have hb : j.val - (pre ++ [a]).length < middle.length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hshape : out = (pre ++ [a]) ++ (middle ++ a :: post) := by
    simpa only [List.append_assoc, List.singleton_append] using he
  have hvj := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position out (pre ++ [a]) middle (a :: post) hshape j
    ⟨j.val - (pre ++ [a]).length, hb⟩ (by
      change j.val = (pre ++ [a]).length + (j.val - (pre ++ [a]).length)
      omega)
  have hv : middle[j.val - (pre ++ [a]).length] = a := hvj.symm.trans (hj.2.trans hvk)
  exact ha (hv ▸ List.getElem_mem hb)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
