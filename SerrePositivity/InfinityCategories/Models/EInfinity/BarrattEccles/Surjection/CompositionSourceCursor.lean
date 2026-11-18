module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowCursorSlot
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationStateSubstitution

/-!
模型。文献の定義との比較は後で
# 元の成功表の行から得る実際の合成行の代入表示

概要：Berger–Fresse §1.5.7 の元の外側抽出状態に内側の現在行と除外状態を代入する。
方針：外側指定値の一出現の分割を元の成功から取り、実際の置換部分合成の行の式へ渡す。
規約：内側 arity 零も同じ表示で扱う。
使われ方：compositionExtractionStep の行の表示仮定を元の二つの表から供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：元の外側行の成功から実際の合成行の一出現代入表示を構成（BF §1.5.7）。
方針：元の利用可能行の指定値の前後を部分型へ持ち上げ、全段階の合成行の式へ代入する。
規約：外側の除外状態・前半長は元の抽出証跡そのもの。
使われ方：三種類の合成抽出の成功規則へ、追加の行表示仮定なしに具体入力を与える。 -/
lemma composite_available_slot_split {m n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d}
    {i : Fin (d + 1)} {v : Fin (m + 1 + d) → Fin (m + 1)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v)) (p : Fin (m + 1 + d))
    (j : Fin (r.val i).val) (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j.val)
    (k : Fin (m + 1)) (hk : v p = k) (τ : Equiv.Perm (Fin n)) (inner : List (Fin n)) :
    ∃ pre post : List {a : Fin (m + 1) // a ≠ k},
      pre.length = j.val ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i) = pre.map Subtype.val ++ k :: post.map Subtype.val ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k b.removed inner)
        (List.ofFn (permutationComposition m n k (w i) τ).symm) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val)
        [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm)] := by
  obtain ⟨pre, post, hs, hl⟩ := b.available_slot_split p j hp k hk
  refine ⟨pre, post, hl, hs, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_state_available_substitute]
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)) _ = _
  rw [hs]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor
