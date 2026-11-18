module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.InsertedOccurrences

/-!
模型。文献の定義との比較は後で
# 解放値の唯一の後続出現

概要：Berger–Fresse §1.4.4 の逆構成で行内の出現と挿入点を一致させる。
方針：指定した先行語の後にある値の出現を中間語・挿入点・後続語へ分類する。
規約：指定先行語には同じ値が含まれてよい。
使われ方：延長行で選択される解放値が構成済みの挿入点であることを示す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：先行語より後の挿入値の出現は指定した挿入点だけ（BF §1.4.4）。
方針：挿入点の前後のどちらでも不出現条件に矛盾する。
規約：先行語の値については制約しない。
使われ方：延長行内の値の所属を挿入点の座標の所属へ移す。 -/
lemma unique_insert_after_prefix {n : ℕ} (out pre middle post : List (Fin n)) (a : Fin n)
    (he : out = pre ++ (middle ++ a :: post)) (hm : a ∉ middle) (ht : a ∉ post)
    (j : Fin out.length) (hlo : pre.length ≤ j.val) (hv : out[j.val] = a) :
    j.val = pre.length + middle.length := by
  rcases lt_trichotomy j.val (pre.length + middle.length) with hlt | heq | hgt
  · have hb : j.val - pre.length < middle.length := by omega
    have heval := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position out pre middle (a :: post) he j
      ⟨j.val - pre.length, hb⟩ (by
        change j.val = pre.length + (j.val - pre.length)
        omega)
    have hvalue : middle[j.val - pre.length] = a := heval.symm.trans hv
    exact False.elim (hm (hvalue ▸ List.getElem_mem hb))
  · exact heq
  · have hs : out = ((pre ++ middle) ++ [a]) ++ post := by
      simpa only [List.append_assoc, List.singleton_append] using he
    have hbound : ((pre ++ middle) ++ [a]).length ≤ j.val := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hmem := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_mem_suffix out _ post hs j hbound
    exact False.elim (ht (hv ▸ hmem))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
