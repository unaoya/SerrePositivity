module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionCorrespondence

/-!
模型。文献の定義との比較は後で
# 残余最終出現削除と区切り削除の全単射

概要：Berger–Fresse §1.4.4 の全ての相殺添字の二方向の逆関係を束ねる。
方針：順から逆の探索の一意性と逆から順の二行の一意性を使う。
規約：全 arity・全次数で退化出力を含めて比較する。
使われ方：残余全体の有限和の相殺の添字変更を与える。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：順方向の対応の後で逆方向へ戻ると元の最終出現削除（BF §1.4.4）。
方針：順から逆の二行・成功出力・削除位置の復元を削除点の外延性へ渡す。
規約：証明書の選択に依存しない。
使われ方：二方向の対応の一方の逆関係。 -/
lemma backward_forwardDeletion {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletion w) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletion (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.forwardDeletion p) = p := by
  let f := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.forwardDeletionData p
  let rb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletionData f.target
  have hs := f.block.reverse_search p.val.success f.order f.long p.val.position f.lower f.upper
    p.property.2.1 p.property.2.2 f.previous f.output f.success f.position f.position_value rb
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reverse_schedule_eq p.val.schedule f.donor f.receiver f.order f.long
    rb.early rb.late rb.order rb.long hs.2.1 hs.2.2
  have ht := f.block.reverse_result p.val.success f.order f.long p.val.position f.lower f.upper
    p.property.2.1 p.property.2.2 f.previous f.output f.success f.position f.position_value rb
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.ext
  · exact hr
  · exact ht.2

/-- 概要：逆方向の対応の後で順方向へ戻ると元の区切り削除（BF §1.4.4）。
方針：逆構成の挿入点の二行の一意性で順方向の二行を同定する。
規約：全ての構成された成功出力を扱う。
使われ方：二方向の対応のもう一方の逆関係。 -/
lemma forward_backwardDeletion {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    (q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CaesuraDeletion w) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.forwardDeletion (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletion q) = q := by
  let rb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletionData q
  let p := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reverseDeletionTarget q rb
  let f := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.forwardDeletionData p
  have hs := rb.forward_rows p.property.2.2 f.donor f.receiver f.lower f.upper f.previous
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.ext
  · change f.schedule = q.val.schedule
    dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ForwardDeletionData.schedule]
    simp only [hs.1, hs.2]
    exact rb.forward_schedule _
  · change f.position.val = q.val.position.val
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset p.val.schedule f.receiver.castSucc +
          (p.val.schedule.val f.receiver.castSucc).val := f.position_value
      _ = _ := by simpa only [p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reverseDeletionTarget, hs.2] using rb.forward_position

/-- 概要：残余の最終出現削除と区切り削除は全単射（BF §1.4.4）。
方針：実際の二方向の成功構成と検証済みの往復等式を束ねる。
規約：零係数の孤立した出現以外の全残余削除を含む。
使われ方：全残余和の二項ずつの相殺に用いる。 -/
def deletionEquiv {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletion w ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CaesuraDeletion w where
  toFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.forwardDeletion
  invFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletion
  left_inv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backward_forwardDeletion
  right_inv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.forward_backwardDeletion

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
