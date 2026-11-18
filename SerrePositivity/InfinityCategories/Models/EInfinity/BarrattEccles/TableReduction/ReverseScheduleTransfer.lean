module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NonfinalRowPrefix
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseBlock
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ResidualRowEnds
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransferPrefixLift

/-!
模型。文献の定義との比較は後で
# 残余の行末削除から実際の逆 Schedule を構成する

概要：Berger–Fresse §1.4.4 の逆ブロックを元の Schedule の添字と全出力へ移す。
方針：探索の停止行の位置を有限列で照合し、二行更新と先行抽出を連結する。
規約：変更後の Schedule の抽出成功や削除後出力一致を仮定しない。
使われ方：行末側からの実際の削除対と順方向との一致を証明する基礎となる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：残余の行末削除から構成した逆 Schedule と語・位置・探索の証明書（BF §1.4.4）。
方針：短縮行と延長行、成功出力、解放値の前後の不出現と探索を保持する。
規約：全データは元の成功抽出から構成する。
使われ方：変更後の挿入位置が最終出現であることと対の逆対応を検証する。 -/
structure ReverseTransferData {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (q : Fin out.length) where
  early : Fin d
  late : Fin (d + 1)
  order : early.castSucc < late
  long : 1 < (r.val early.castSucc).val
  row_end : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r early = q.val
  context : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NonfinalRowPrefix w r early out
  a : Fin n
  b : Fin n
  earlier : List (List (Fin n) × ℕ)
  selected : List (List (Fin n))
  finish : List (Fin n)
  chosen : List (Fin n) × ℕ
  later : List (List (Fin n) × ℕ)
  free : List (Fin n)
  free_state : free = context.removed ++
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available context.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w early.castSucc)).take
      (((r.val early.castSucc).val - 1) - 1)
  search : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a context.after free earlier selected finish chosen later
  late_index : late.val = context.before.length + 1 + earlier.length
  left : List (Fin n)
  middle : List (Fin n)
  right : List (Fin n)
  left_end : ∃ head, left = head ++ [a]
  distinct : a ≠ b
  absent_middle : a ∉ middle
  absent_right : a ∉ right
  left_length : left.length = (r.val early.castSucc).val - 1
  new : List (Fin n)
  point : Fin new.length
  success : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r early.castSucc late (ne_of_lt order) long)) [] = some new
  source_shape : out = context.picked.flatten ++ (left ++ b :: (middle ++ right))
  target_shape : new = context.picked.flatten ++ (left ++ (middle ++ a :: right))
  point_value : point.val = q.val + middle.length
  deleted_eq : out.eraseIdx q.val = new.eraseIdx point.val

/-- 概要：全ての残余の区切り削除から実際の逆 Schedule の成功と削除後出力一致（BF §1.4.4）。
方針：元の非最終行で切り、逆ブロックの結果を二つの有限行添字へ戻す。
規約：退化出力も含み、相手の成功・出力一致を追加仮定しない。
使われ方：行末側の削除対を順方向と比較するための完全な抽出データを与える。 -/
lemma reverseTransferData_nonempty {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (q : Fin out.length) (hx : q ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h))
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) q) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w r out q) := by
  obtain ⟨i, hrowEnd, hlong⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.residual_caesura_row w r out h q hx hc
  obtain ⟨p⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nonfinalRowPrefix_nonempty w r i out h
  obtain ⟨a, b, earlier, picked, finish, chosen, later, left, mid, right, free,
    hs, hfreeState, hleftEnd, hab, haMid, haRight, hleft, hold, hnew, hdel⟩ :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reverse_block_extraction p.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc) (r.val i.castSucc).val
        p.after p.localOut p.removed_nodup (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow_nodup w i.castSucc) hlong
        p.after_nonempty p.after_complete p.success p.budget
  have hsplit : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = p.before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val) ::
      (earlier ++ chosen :: later) := by rw [p.split, hs.decomposition]
  have hlen := congrArg List.length hsplit
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn, List.length_append, List.length_cons] at hlen
  let j : Fin (d + 1) := ⟨p.before.length + 1 + earlier.length, by omega⟩
  have ho : i.castSucc < j := by
    change i.val < p.before.length + 1 + earlier.length
    have := p.before_length
    omega
  have hdonorSplit : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r =
      (p.before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val) :: earlier) ++
        chosen :: later := by
    simpa only [List.append_assoc, List.cons_append] using hsplit
  have hchosen : chosen = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w j, (r.val j).val) :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ofFn_value_at_split (fun k => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w k, (r.val k).val)) _ _ chosen hdonorSplit j (by
      simp only [List.length_append, List.length_cons]
      dsimp only [j]
      omega)
  have hfullSplit : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = p.before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val) ::
      (earlier ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w j, (r.val j).val) :: later) := by rw [← hchosen]; exact hsplit
  have hnewRows := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_reverse_transfer_blocks w r i.castSucc j (ne_of_lt ho) hlong
    p.before earlier later hfullSplit p.before_length (by rfl)
  have hnewLocal : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r.val i.castSucc).val - 1) ::
      (earlier ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w j, (r.val j).val + 1) :: later)) p.removed =
        some (left ++ (mid ++ a :: right)) := by simpa only [hchosen] using hnew
  have hnewFull := p.trace.append _ _ hnewLocal
  let new := p.picked.flatten ++ (left ++ (mid ++ a :: right))
  have hsuccess : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r i.castSucc j (ne_of_lt ho) hlong)) [] = some new := by
    rw [hnewRows]
    exact hnewFull
  have hsource : out = p.picked.flatten ++ (left ++ b :: (mid ++ right)) :=
    p.output_eq.trans (congrArg (List.append p.picked.flatten) hold)
  have hq : q.val = p.picked.flatten.length + ((r.val i.castSucc).val - 1) := by
    have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one r i
    have hp := p.prefix_length
    omega
  have hnewLen : new.length = p.picked.flatten.length +
      (left.length + (mid.length + 1 + right.length)) := by
    simp only [new, List.length_append, List.length_cons]
    omega
  let k : Fin new.length := ⟨q.val + mid.length, by omega⟩
  have hdeleted : out.eraseIdx q.val = new.eraseIdx k.val := by
    calc
      _ = (p.picked.flatten ++ p.localOut).eraseIdx q.val :=
        congrArg (fun xs => xs.eraseIdx q.val) p.output_eq
      _ = p.picked.flatten ++ p.localOut.eraseIdx ((r.val i.castSucc).val - 1) := by
        rw [hq, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.eraseIdx_prefix_add]
      _ = p.picked.flatten ++ (left ++ (mid ++ a :: right)).eraseIdx
          ((r.val i.castSucc).val - 1 + mid.length) := by rw [hdel]
      _ = _ := by
        change _ = (p.picked.flatten ++ (left ++ (mid ++ a :: right))).eraseIdx
          (q.val + mid.length)
        rw [hq, Nat.add_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.eraseIdx_prefix_add]
  exact ⟨⟨i, j, ho, hlong, hrowEnd, p, a, b, earlier, picked, finish, chosen, later, free,
    hfreeState, hs, rfl, left, mid, right, hleftEnd, hab, haMid, haRight, hleft, new, k, hsuccess,
    hsource, rfl, rfl, hdeleted⟩⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
