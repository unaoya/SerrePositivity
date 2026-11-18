module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ForwardDeletionData

/-!
模型。文献の定義との比較は後で
# 残余削除の二方向の対応

概要：Berger–Fresse §1.4.4 の二種類の削除点の間の実際の写像を定義する。
方針：検証済みの成功構成から一つの証明書を取り、残余条件とともに束ねる。
規約：選択した証明書に依存しない逆関係は別に証明する。
使われ方：有限和を添字変更する全単射を組み立てる。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：各残余最終出現削除の順方向データ（BF §1.4.4）。
方針：既存の存在証明から選ぶ。
規約：成功や位置の条件を新しい仮定にしない。
使われ方：順方向の対応の定義。 -/
def forwardDeletionData {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletion w) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ForwardDeletionData p :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.forwardDeletionData_nonempty p)

/-- 概要：各残余区切り削除の逆方向データ（BF §1.4.4）。
方針：元の成功と残余区切り条件から逆構成の存在を適用する。
規約：変更後の成功は逆構成の定理で保証する。
使われ方：逆方向の対応の定義。 -/
def backwardDeletionData {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    (q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CaesuraDeletion w) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w q.val.schedule q.val.output q.val.position :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reverseTransferData_nonempty w q.val.schedule q.val.output q.val.success
    q.val.position q.property.1 q.property.2)

/-- 概要：逆構成の相手は先行出現を持つ残余最終出現削除（BF §1.4.4）。
方針：逆構成の成功・残余所属・最終出現と直前出現を束ねる。
規約：退化出力も保持する。
使われ方：逆方向の写像の値域を与える。 -/
def reverseDeletionTarget {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    (q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CaesuraDeletion w)
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w q.val.schedule q.val.output q.val.position) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletion w := by
  refine ⟨⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer q.val.schedule b.early.castSucc b.late
    (ne_of_lt b.order) b.long, b.new, b.success, b.point⟩, ?_, b.point_not_caesura, ?_⟩
  · exact b.point_not_singleton _
  · exact b.point_previousOccurrence.choose

/-- 概要：残余最終出現削除から残余区切り削除への写像（BF §1.4.4）。
方針：選択した順方向データの実際の相手を取る。
規約：全ての arity・次数に適用する。
使われ方：相殺の有限和の添字変更。 -/
def forwardDeletion {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletion w) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CaesuraDeletion w := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.forwardDeletionData p).target

/-- 概要：残余区切り削除から残余最終出現削除への写像（BF §1.4.4）。
方針：選択した逆方向データの実際の相手を取る。
規約：相手の成功・残余所属を仮定しない。
使われ方：相殺の全単射の逆写像。 -/
def backwardDeletion {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    (q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CaesuraDeletion w) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletion w := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reverseDeletionTarget q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletionData q)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
