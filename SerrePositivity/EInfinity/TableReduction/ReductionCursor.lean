module

public import SerrePositivity.EInfinity.Surjection.CompositionSourceCursor

/-!
# 元の語の位置における具体的な抽出状態

概要：Berger–Fresse §1.5.7 の語の位置から元の一行の抽出状態を構成する。
方針：語で決まる所属行と行内添字を、同じ元の成功から取り出した一行の状態に適用する。
規約：証明書の選択だけを非計算的に行い、行・列の自然数値は既存の計算値を使う。
使われ方：内外成分の端点から実際の合成行の三ブロック表示を直接得る。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection BarrattEccles

/-- 概要：元の出力位置の所属行における抽出状態（BF §1.5.7）。
方針：同じ成功証明から所属行の一行の証明書を取り出す。
規約：所属行は reductionRow で固定し、任意に選ばない。
使われ方：成分端点の前後の元の状態を一つの公開名で参照する。 -/
noncomputable def reductionCursor {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) : ScheduleRowCursor w r (reductionRow w r v h p) (List.ofFn v) :=
  Classical.choice (scheduleRowCursor_nonempty w r (reductionRow w r v h p) (List.ofFn v) h)

/-- 概要：元の指定出力文字はその位置の実際の除外状態に含まれない（BF §1.5.7）。
方針：所属行と行内添字で利用可能行の値を照合する。
規約：最終行末や退化出力も含む。
使われ方：合成行の指定値の未除外条件を元の成功だけから得る。 -/
lemma reductionCursor_value_not_removed {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) : v p ∉ (reductionCursor w r v h p).removed :=
  (reductionCursor w r v h p).value_not_removed p (reductionColumn w r v h p)
    (reductionColumn_position w r v h p)

/-- 概要：元の指定出力位置から実際の合成行の一出現代入表示を得る（BF §1.5.7）。
方針：同じ元の成功から行・列・除外状態を固定し、内側の現在行を代入する。
規約：行表示や外側の未除外性を別途仮定しない。
使われ方：成分端点から三種類の合成抽出の成功規則を具体的に準備する。 -/
lemma reductionCursor_composite_row {m n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (r : Schedule (m + 1) d)
    (v : Fin (m + 1 + d) → Fin (m + 1))
    (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (p : Fin (m + 1 + d)) (k : Fin (m + 1)) (hk : v p = k)
    (τ : Equiv.Perm (Fin n)) (inner : List (Fin n)) :
    ∃ pre post : List {a : Fin (m + 1) // a ≠ k},
      pre.length = (reductionColumn w r v h p).val ∧
      available (reductionCursor w r v h p).removed
        (vertexRow w (reductionRow w r v h p)) =
        pre.map Subtype.val ++ k :: post.map Subtype.val ∧
      available (compositionStateRemoved k (reductionCursor w r v h p).removed inner)
        (List.ofFn (permutationComposition m n k (w (reductionRow w r v h p)) τ).symm) =
      substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val)
        [available inner (List.ofFn τ.symm)] :=
  (reductionCursor w r v h p).composite_available_slot_split p (reductionColumn w r v h p)
    (reductionColumn_position w r v h p) k hk τ inner

end SerrePositivity.EInfinity.TableReduction
