module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReorderedBoundary

/-!
模型。文献の定義との比較は後で
# 中央ブロックの並べ替えと非退化出力の行末

概要：Berger–Fresse §1.5.8 の固定外側頂点の連続行に対する行末制約を証明する。
方針：外側末尾の位置で前後を分け、前半の所属集合の一致へ帰着する。
規約：中央ブロックは順序だけが変わり、外側の前後ブロックは一致する。
使われ方：任意の非退化な合成 table から元の内側抽出を復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：中央部分だけを並べ替えた二行の外側末尾は重複を生む（BF §1.5.8）。
方針：末尾が前半か後半かで分け、境界以前の文字の所属集合を比較する。
規約：第一行は非重複。第二行の中央は同じ所属集合を持てばよい。
使われ方：非退化出力での中間行の外側末尾を排除する。 -/
lemma reduceRows_block_external_endpoint_not_isChain (pre middle middle' post : List α)
    (hm : ∀ x, x ∈ middle' ↔ x ∈ middle) (hn : (pre ++ middle ++ post).Nodup)
    (removed out : List α) (a : α) (r s : ℕ) (rest : List (List α × ℕ))
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ middle ++ post))[r - 1]? = some a)
    (ha : a ∈ pre ++ post)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((pre ++ middle ++ post, r) ::
      (pre ++ middle' ++ post, s) :: rest) removed = some out) :
    ¬ out.IsChain (· ≠ ·) := by
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨left, right, rfl⟩ := List.mem_iff_append.mp ha
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_reordered_endpoint_not_isChain left left a
      (right ++ middle ++ post) (right ++ middle' ++ post) (fun _ => Iff.rfl)
      (by simpa only [List.append_assoc, List.cons_append] using hn)
      removed out r s rest
    · simpa only [List.append_assoc, List.cons_append] using he
    · simpa only [List.append_assoc, List.cons_append] using h
  · obtain ⟨left, right, rfl⟩ := List.mem_iff_append.mp ha
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_reordered_endpoint_not_isChain (pre ++ middle ++ left)
      (pre ++ middle' ++ left) a right right
      (fun x => by simp only [List.mem_append, hm])
      (by simpa only [List.append_assoc] using hn) removed out r s rest
      (by simpa only [List.append_assoc] using he)
      (by simpa only [List.append_assoc] using h)

/-- 概要：非退化な成功出力では前行末は中央ブロックに属する（BF §1.5.8）。
方針：行末は元の行に属し、外側に属すれば次行との境界で重複する。
規約：既除外集合は任意。後続 table 全体の成功と非退化性から結論する。
使われ方：固定した外側置換の垂直連続行の内側末尾を得る。 -/
lemma reduceRows_block_endpoint_mem_middle (pre middle middle' post : List α)
    (hm : ∀ x, x ∈ middle' ↔ x ∈ middle) (hn : (pre ++ middle ++ post).Nodup)
    (removed out : List α) (a : α) (r s : ℕ) (rest : List (List α × ℕ))
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ middle ++ post))[r - 1]? = some a)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((pre ++ middle ++ post, r) ::
      (pre ++ middle' ++ post, s) :: rest) removed = some out)
    (hc : out.IsChain (· ≠ ·)) : a ∈ middle := by
  have ha := List.mem_of_mem_filter (List.mem_of_getElem? he)
  by_contra hmid
  have hext : a ∈ pre ++ post := by
    simpa only [List.mem_append, hmid, or_false] using ha
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_block_external_endpoint_not_isChain pre middle middle' post hm hn
    removed out a r s rest he hext h hc

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
