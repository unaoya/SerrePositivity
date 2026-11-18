module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseResidual
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseDeletionPair

/-!
模型。文献の定義との比較は後で
# 逆構成の後で順方向へ戻ると元の削除対

概要：Berger–Fresse §1.4.4 の逆構成に対する順方向の一意性を検証する。
方針：挿入点の所属行と直前出現の行末の一意性から二行を同定する。
規約：逆構成の出力を始点とする向きの往復だけをここで扱う。
使われ方：二種類の残余削除の全単射の一方の逆関係を与える。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

namespace ReverseTransferData

variable {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
  {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {out : List (Fin n)} {q : Fin out.length}

/-- 概要：逆構成の後の順方向の二行は延長行・短縮行に一意（BF §1.4.4）。
方針：挿入点の行内範囲と直前出現の行末をそれぞれ単射性で比較する。
規約：順方向の二行の選択方法には依存しない。
使われ方：順方向で実際に移す Schedule が元へ戻ることを示す。 -/
lemma forward_rows (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin b.new.length => b.new[j.val]) b.point).Nonempty)
    (donor : Fin (d + 1)) (receiver : Fin d)
    (hlo : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late
      (ne_of_lt b.order) b.long) donor ≤ b.point.val)
    (hhi : b.point.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late
      (ne_of_lt b.order) b.long) donor +
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late
          (ne_of_lt b.order) b.long).val donor).val)
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late
      (ne_of_lt b.order) b.long) receiver =
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin b.new.length => b.new[j.val]) b.point).max' hp).val) :
    donor = b.late ∧ receiver = b.early := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.row_unique_of_bounds _ donor b.late b.point.val hlo hhi
    b.point_in_late_row.1 b.point_in_late_row.2, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_injective
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late (ne_of_lt b.order) b.long)
  obtain ⟨hp', hprev⟩ := b.point_previousOccurrence
  have hend := b.shortened_end
  have hproof : hp' = hp := Subsingleton.elim _ _
  rw [hproof] at hprev
  omega

/-- 概要：逆構成から順方向で移すと元の Schedule（BF §1.4.4）。
方針：二行の一意性と行長移動の逆公式を用いる。
規約：順方向の長さの証明項の選び方には依存しない。
使われ方：成功出力の一意性と合わせ、逆から順の往復を検証する。 -/
lemma forward_schedule (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q)
    (hd : 1 < ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late
      (ne_of_lt b.order) b.long).val b.late).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late (ne_of_lt b.order) b.long)
      b.late b.early.castSucc (ne_of_gt b.order) hd = r := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_inverse r b.early.castSucc b.late (ne_of_lt b.order) b.long

/-- 概要：逆から順の往復で行末の位置も元へ戻る（BF §1.4.4）。
方針：短縮後の行末＋1 を、順方向の新しい行末の公式へ戻す。
規約：元の削除位置 q は零始まり。
使われ方：往復の Schedule だけでなく削除位置も同じであることを保証する。 -/
lemma forward_position (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late
      (ne_of_lt b.order) b.long) b.early.castSucc +
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r b.early.castSucc b.late
        (ne_of_lt b.order) b.long).val b.early.castSucc).val = q.val := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one]
  exact b.shortened_end

end ReverseTransferData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
