module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.FirstOccurrenceSteps

/-!
模型。文献の定義との比較は後で
# 復元行の一文字の通過による変化

概要：Berger–Fresse §1.4.2–3 の復元行の局所的な移動則を証明する。
方針：確定した前半の変化と、残りの語の最初の出現の変化を合わせる。
規約：最終出現を通過すると行は不変、再出現する文字は後方へ戻る。
使われ方：標準頂点列の隣接行の一文字の移動と境界選択の一意性を導く。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {α : Type*} [DecidableEq α]

/-- 概要：確定した最終出現の前半への一文字の追加（BF §1.4.2）。
方針：末尾追加の重複除去と後続語での所属条件を比較する。
規約：後続に同値があれば前半は不変、なければ末尾へ加える。
使われ方：位置を一つ進めたときの pastFinals を計算する。 -/
lemma finalizedPrefix_append (pre tail : List α) (a : α) :
    (pre ++ [a]).dedup.filter (fun x => x ∉ tail) =
      pre.dedup.filter (fun x => x ∉ a :: tail) ++ if a ∈ tail then [] else [a] := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.dedup_append_singleton, List.filter_append]
  congr 1
  · simp only [List.filter_filter]
    apply List.filter_congr
    intro x _
    by_cases hxa : x = a <;> by_cases hx : x ∈ tail <;> simp [hxa, hx]
  · by_cases ha : a ∈ tail <;> simp [ha]

/-- 概要：位置を一つ進めた確定済みの値の列（BF §1.4.2）。
方針：take の末尾追加と drop の先頭除去を前半の追加の式へ代入する。
規約：位置 p の文字が範囲内にあるとする。
使われ方：復元行の一文字の変化を述べる。 -/
lemma pastFinals_succ (xs : List α) (p : ℕ) (hp : p < xs.length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs (p + 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs p ++
      if xs[p] ∈ xs.drop (p + 1) then [] else [xs[p]] := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals
  rw [← List.take_concat_get' xs p hp, List.drop_eq_getElem_cons hp]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.finalizedPrefix_append _ _ _

/-- 概要：再出現する文字を通過しても確定した前半は不変（BF §1.4.2）。
方針：前半の追加の式の空の分岐を使う。
規約：後続語に同値が存在する。
使われ方：区切りで移動する文字以外の前半を固定する。 -/
lemma pastFinals_succ_of_mem (xs : List α) (p : ℕ) (hp : p < xs.length)
    (ha : xs[p] ∈ xs.drop (p + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs (p + 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs p := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals_succ xs p hp, ite_eq_left ha, List.append_nil]

/-- 概要：最終出現の通過で復元行は変わらない（BF §1.4.2）。
方針：前半に加えた文字は、それまでの後半の先頭の文字と同じ。
規約：後続語に同値が存在しない。
使われ方：連続する最終出現の位置で復元行をまとめて比較する。 -/
lemma canonicalRow_succ_of_not_mem (xs : List α) (p : ℕ) (hp : p < xs.length)
    (ha : xs[p] ∉ xs.drop (p + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs (p + 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs p := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals_succ xs p hp, ite_eq_right ha, List.drop_eq_getElem_cons hp,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences_cons_of_not_mem _ _ ha]
  simp only [List.append_assoc, List.singleton_append]

/-- 概要：区切りの直前の行は文字を前へ出した列（BF §1.4.2–3）。
方針：前半を固定し、最初の出現の先頭の式を使う。
規約：後続にある同値は除去して、先頭の一つだけを残す。
使われ方：隣接する復元行の一文字の移動を明示する。 -/
lemma canonicalRow_before_step (xs : List α) (p : ℕ) (hp : p < xs.length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs p ++ xs[p] ::
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences (xs.drop (p + 1))).filter (fun x => x ≠ xs[p]) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow, List.drop_eq_getElem_cons hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences_cons]

/-- 概要：区切りの直後の行は文字を後方へ戻した列（BF §1.4.2–3）。
方針：確定した前半の不変性と後続の最初の出現を合わせる。
規約：再出現する文字は後半の本来の順序で一度だけ現れる。
使われ方：区切りの前後を一文字の移動として比較する。 -/
lemma canonicalRow_after_step_of_mem (xs : List α) (p : ℕ) (hp : p < xs.length)
    (ha : xs[p] ∈ xs.drop (p + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow xs (p + 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals xs p ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences (xs.drop (p + 1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals_succ_of_mem xs p hp ha]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
