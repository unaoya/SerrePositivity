module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseOccurrences
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PrefixSuccess

/-!
模型。文献の定義との比較は後で
# 逆 Schedule の延長行までの実際の先行抽出

概要：Berger–Fresse §1.4.4 の逆探索の停止状態を全 table の状態に同定する。
方針：元の先行抽出と短縮行、探索の先行証跡を連結する。
規約：変更後の成功は既に構成した実際の逆 Schedule のもの。
使われ方：挿入点が長い延長行に属することの検証へ状態と出力を供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

namespace ReverseTransferData

variable {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
  {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {out : List (Fin n)} {q : Fin out.length}

/-- 概要：探索の停止行は指定した後続の頂点と元の行長（BF §1.4.4）。
方針：有限列の分割と停止行の添字を評価する。
規約：同じ頂点が他の行にあってもよい。
使われ方：探索の停止条件を実際の延長行へ移す。 -/
lemma chosen_eq (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    b.chosen = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.late, (r.val b.late).val) := by
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = b.context.before ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.early.castSucc, (r.val b.early.castSucc).val) ::
        (b.earlier ++ b.chosen :: b.later) := by
    rw [b.context.split, b.search.decomposition]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ofFn_value_at_split (fun k => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w k, (r.val k).val))
    (b.context.before ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.early.castSucc, (r.val b.early.castSucc).val) :: b.earlier) b.later b.chosen
    (by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow, List.append_assoc, List.cons_append] using he) b.late (by
      simp only [List.length_append, List.length_cons]
      have := b.late_index
      omega)

/-- 概要：逆 Schedule の行リストを実際の短縮行と延長行で分割（BF §1.4.4）。
方針：探索の停止行を同定して二行更新を評価する。
規約：先行・中間・後続の行は元と同じ。
使われ方：先行抽出証跡と変更後の全成功を結ぶ。 -/
lemma changed_rows (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late (ne_of_lt b.order) b.long) =
      b.context.before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.early.castSucc, (r.val b.early.castSucc).val - 1) ::
        (b.earlier ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.late, (r.val b.late).val + 1) :: b.later) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_reverse_transfer_blocks w r b.early.castSucc b.late
    (ne_of_lt b.order) b.long b.context.before b.earlier b.later
  · rw [b.context.split, b.search.decomposition, b.chosen_eq]
  · exact b.context.before_length
  · exact b.late_index.symm

/-- 概要：変更後の table の延長行直前までの抽出証跡（BF §1.4.4）。
方針：短縮行の次の状態を解放状態と照合して探索を連結する。
規約：証跡の終端は探索の finish そのもの。
使われ方：延長行に含まれる解放値を変更後の全出力へ移す。 -/
lemma to_chosen_prefix (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (b.context.before ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.early.castSucc, (r.val b.early.castSucc).val - 1) :: b.earlier) []
      (b.context.picked ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.context.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w b.early.castSucc)).take
          ((r.val b.early.castSucc).val - 1) :: b.selected) b.finish := by
  obtain ⟨_, hb, _, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ b.context.success
  apply b.context.trace.trans
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.cons
  · have := b.long; omega
  · omega
  · rw [← b.free_state]
    exact b.search.toPrefix

end ReverseTransferData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
