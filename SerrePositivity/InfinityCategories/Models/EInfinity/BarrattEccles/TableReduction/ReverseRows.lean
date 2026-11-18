module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock

/-!
模型。文献の定義との比較は後で
# 先行行の短縮と後続行の延長を実際の Schedule に移す

概要：Berger–Fresse §1.4.4 の逆の行長移動を行リストの二つの更新と同定する。
方針：元の有限列の指定値を分割から読み、先の set と後の set を評価する。
規約：短くする行が先、延ばす行が後。
使われ方：逆探索の停止行を実際の Schedule の添字へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：分割された有限列の指定位置の値は元の有限関数の値（BF §1.4.4）。
方針：先行部分の長さで Option の添字を評価する。
規約：元の行の重複の有無には依存しない。
使われ方：逆探索で選んだ行を実際の頂点と行長の対へ戻す。 -/
lemma ofFn_value_at_split {α : Type*} {m : ℕ} (f : Fin m → α)
    (before after : List α) (x : α) (he : List.ofFn f = before ++ x :: after)
    (i : Fin m) (hi : before.length = i.val) : x = f i := by
  have ht := congrArg (fun xs => xs[before.length]?) he
  have hb : before.length < m := by have := i.isLt; omega
  rw [List.getElem?_ofFn, dite_eq_left hb] at ht
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero] at ht
  have hidx : (⟨before.length, hb⟩ : Fin m) = i := Fin.ext hi
  simpa only [hidx, Option.some.injEq] using ht.symm

/-- 概要：先行行を更新してから後続行を更新しても同じ分割を保つ（BF §1.4.4）。
方針：二つの set を前・中の長さだけ移す。
規約：二行は異なり、中間部分は空でもよい。
使われ方：逆向きの Schedule の変更後リストを同定する。 -/
lemma set_two_row_blocks_reverse {α : Type*} (before middle after : List α)
    (x y x' y' : α) :
    (((before ++ x :: (middle ++ y :: after)).set before.length x').set
      (before.length + 1 + middle.length) y') = before ++ x' :: (middle ++ y' :: after) := by
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]
  rw [List.set_append_right _ _ (by omega)]
  have he : before.length + 1 + middle.length - before.length = middle.length + 1 := by omega
  rw [he, List.set_cons_succ, List.set_append_right _ _ (Nat.le_refl _),
    Nat.sub_self, List.set_cons_zero]

/-- 概要：逆向きの Schedule は先行行を 1 短縮し後続行を 1 延長する（BF §1.4.4）。
方針：一般の二行更新を、短縮行が先になるリストの分割で評価する。
規約：現在の Schedule の先行行の長さは 2 以上。
使われ方：逆ブロックの成功抽出を実際の相手の Schedule と同定する。 -/
lemma rows_reverse_transfer_blocks {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (early late : Fin (d + 1)) (hne : early ≠ late) (hr : 1 < (r.val early).val)
    (before middle after : List (List (Fin n) × ℕ))
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w early, (r.val early).val) ::
      (middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w late, (r.val late).val) :: after))
    (hb : before.length = early.val) (hm : before.length + 1 + middle.length = late.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r early late hne hr) = before ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w early, (r.val early).val - 1) ::
        (middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w late, (r.val late).val + 1) :: after) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_deletionScheduleTransfer, he, ← hb, ← hm]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.set_two_row_blocks_reverse before middle after _ _ _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
