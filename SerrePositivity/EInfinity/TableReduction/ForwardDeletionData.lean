module

public import SerrePositivity.EInfinity.TableReduction.DeletionPoint

/-!
# 残余最終出現削除の実際の順方向データ

概要：Berger–Fresse §1.4.4 の順方向の相殺相手と二行の位置を束ねる。
方針：既存の成功構成からデータを取り、新しい行末を残余の区切り削除とする。
規約：相手の成功・残余所属を仮定せず構成する。
使われ方：二種類の有限削除型の対応と逆関係を定義する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：残余最終出現削除の行長移動の証明書（BF §1.4.4）。
方針：二行と成功出力、元の削除位置と直前出現の位置を保持する。
規約：元の点は先行出現を持つ最終出現削除。
使われ方：順方向の対応を選択し、その逆関係を一意性で検証する。 -/
structure ForwardDeletionData {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    (p : FinalDeletion w) where
  donor : Fin (d + 1)
  receiver : Fin d
  order : receiver.castSucc < donor
  long : 1 < (p.val.schedule.val donor).val
  output : List (Fin n)
  lower : scheduleOffset p.val.schedule donor ≤ p.val.position.val
  upper : p.val.position.val < scheduleOffset p.val.schedule donor +
    (p.val.schedule.val donor).val
  previous : scheduleEnd p.val.schedule receiver =
    ((previousOccurrences (fun j : Fin p.val.output.length => p.val.output[j.val])
      p.val.position).max' p.property.2.2).val
  success : reduceRows (rows w (deletionScheduleTransfer p.val.schedule donor receiver.castSucc
    (ne_of_gt order) long)) [] = some output

/-- 概要：全ての残余最終出現削除から順方向データを構成（BF §1.4.4）。
方針：全ての位置を扱う final_deletion_transfer をそのまま束ねる。
規約：退化出力も保持する。
使われ方：順方向の相殺対応の存在。 -/
lemma forwardDeletionData_nonempty {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    (p : FinalDeletion w) : Nonempty (ForwardDeletionData p) := by
  obtain ⟨donor, receiver, ho, hd, out, hlo, hhi, hp, _, hnew, _⟩ :=
    final_deletion_transfer w p.val.schedule p.val.output p.val.success p.val.position
      p.property.1 p.property.2.1 p.property.2.2
  exact ⟨⟨donor, receiver, ho, hd, out, hlo, hhi, hp, hnew⟩⟩

namespace ForwardDeletionData

variable {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {p : FinalDeletion w}

/-- 概要：順方向データの元の二行の実際の抽出証明書（BF §1.4.4）。
方針：元の成功と二行の順序から既存の証明書を取る。
規約：選択される証明書の違いは抽出の一意性で比較する。
使われ方：順から逆の復元定理を適用する。 -/
def block (b : ForwardDeletionData p) :
    ScheduleBlock w p.val.schedule b.receiver.castSucc b.donor p.val.output :=
  Classical.choice (scheduleBlock_nonempty w p.val.schedule b.receiver.castSucc b.donor
    b.order p.val.output p.val.success)

/-- 概要：順方向データの相手の Schedule（BF §1.4.4）。
方針：削除行から受け取り行へ長さを一つ移す。
規約：二行の相違と削除行の余裕はデータの証明から取る。
使われ方：相手の削除点の Schedule。 -/
def schedule (b : ForwardDeletionData p) : Schedule n d :=
  deletionScheduleTransfer p.val.schedule b.donor b.receiver.castSucc (ne_of_gt b.order) b.long

/-- 概要：相手の削除位置は受け取り行の新しい行末（BF §1.4.4）。
方針：成功出力の長さと次の開始位置の上界を使う。
規約：相手の出力の実際の有限添字。
使われ方：順方向の対応の位置を指定する。 -/
def position (b : ForwardDeletionData p) : Fin b.output.length :=
  ⟨scheduleEnd b.schedule b.receiver, by
    have hl := output_length w b.schedule b.output b.success
    have hb := scheduleOffset_lt b.schedule b.receiver.succ
    have ht := Nat.sub_le (scheduleOffset b.schedule b.receiver.succ) 1
    change scheduleOffset b.schedule b.receiver.succ - 1 < b.output.length
    omega⟩

/-- 概要：相手の削除位置は元の受け取り行の終了境界（BF §1.4.4）。
方針：受け取り行より前の部分和の不変性を使う。
規約：零始まりの削除位置。
使われ方：順から逆の復元で元の行末を指定する。 -/
lemma position_value (b : ForwardDeletionData p) :
    b.position.val = scheduleOffset p.val.schedule b.receiver.castSucc +
      (p.val.schedule.val b.receiver.castSucc).val :=
  b.block.end_transfer_receiver (ne_of_gt b.order) b.long

/-- 概要：順方向の相手は残余の区切り削除（BF §1.4.4）。
方針：延長行の長さは 2 以上で、その行末は区切りである。
規約：相手の退化出力も捨てない。
使われ方：有限削除型の順対応の値域を与える。 -/
def target (b : ForwardDeletionData p) : CaesuraDeletion w := by
  refine ⟨⟨b.schedule, b.output, b.success, b.position⟩, ?_, ?_⟩
  · apply scheduleEnd_not_singleton b.schedule b.receiver _ b.output
      (output_length w b.schedule b.output b.success) b.position rfl
    change 1 < ((deletionScheduleTransfer p.val.schedule b.donor b.receiver.castSucc
      (ne_of_gt b.order) b.long).val b.receiver.castSucc).val
    rw [deletionScheduleTransfer_receiver]
    have := p.val.schedule.property.1 b.receiver.castSucc
    omega
  · exact caesura_of_scheduleEnd w b.schedule b.output b.success b.receiver b.position rfl

end ForwardDeletionData

end SerrePositivity.EInfinity.TableReduction
