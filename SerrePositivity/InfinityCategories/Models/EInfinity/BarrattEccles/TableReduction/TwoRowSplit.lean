module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransferRows

/-!
模型。文献の定義との比較は後で
# 二つの行位置での table の分割

概要：Berger–Fresse §1.4.4 の受け取り行・中間行・削除行を実際のリスト上で指定する。
方針：二つの自然数位置でリストを分割し、有限列の各位置の値へ戻す。
規約：受け取り行は削除行より前にある。
使われ方：元と変更後の Schedule を同じ五部分の行リストで表示する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：二つの順序付き位置でリストを前・二要素・中・後に分ける（BF §1.4.4）。
方針：先頭位置が零になるまでリストで帰納する。
規約：二つの指定位置は必ず異なる。
使われ方：実際の table の二行とその間の行を取り出す。 -/
lemma list_split_two {α : Type*} (xs : List α) (i j : ℕ)
    (hij : i < j) (hj : j < xs.length) :
    ∃ before middle after x y, xs = before ++ x :: (middle ++ y :: after) ∧
      before.length = i ∧ before.length + 1 + middle.length = j := by
  induction xs generalizing i j with
  | nil => simp only [List.length_nil] at hj; omega
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        have hb : j < xs.length := by simp only [List.length_cons] at hj; omega
        refine ⟨[], xs.take j, xs.drop (j + 1), x, xs[j], ?_, rfl, ?_⟩
        · have he : xs = xs.take j ++ xs[j] :: xs.drop (j + 1) := by
            calc
              _ = xs.take j ++ xs.drop j := (List.take_append_drop j xs).symm
              _ = _ := by rw [List.drop_eq_getElem_cons hb]
          simpa only [List.nil_append] using congrArg (List.cons x) he
        · simp only [List.length_nil, List.length_take, Nat.min_eq_left (by omega : j ≤ xs.length)]
          omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        obtain ⟨before, middle, after, a, b, he, hb, hm⟩ := ih i j (by omega) (by
          simp only [List.length_cons] at hj; omega)
        refine ⟨x :: before, middle, after, a, b, ?_, ?_, ?_⟩
        · simpa only [List.cons_append] using congrArg (List.cons x) he
        · simp only [List.length_cons]; omega
        · simp only [List.length_cons]; omega

/-- 概要：有限列の二つの指定値を保つリストの分割（BF §1.4.4）。
方針：分割の要素を Option の評価で元の有限関数と照合する。
規約：分割の前と中の長さを同時に指定する。
使われ方：table の二行を指定した頂点の逆置換の行と同定する。 -/
lemma ofFn_split_two {α : Type*} {m : ℕ} (f : Fin m → α) (i j : Fin m) (hij : i < j) :
    ∃ before middle after, List.ofFn f = before ++ f i :: (middle ++ f j :: after) ∧
      before.length = i.val ∧ before.length + 1 + middle.length = j.val := by
  obtain ⟨before, middle, after, x, y, he, hb, hm⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.list_split_two (List.ofFn f) i.val j.val
    hij (by simpa only [List.length_ofFn] using j.isLt)
  have hx : x = f i := by
    have ht := congrArg (fun xs => xs[before.length]?) he
    have hindex : before.length < m := by omega
    rw [List.getElem?_ofFn, dite_eq_left hindex] at ht
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero] at ht
    have heval : (⟨before.length, hindex⟩ : Fin m) = i := Fin.ext hb
    simpa only [heval, Option.some.injEq] using ht.symm
  have hy : y = f j := by
    have ht := congrArg (fun xs => xs[before.length + 1 + middle.length]?) he
    have hindex : before.length + 1 + middle.length < m := by omega
    rw [List.getElem?_ofFn, dite_eq_left hindex] at ht
    rw [List.getElem?_append_right (by omega)] at ht
    have hsub : before.length + 1 + middle.length - before.length = middle.length + 1 := by
      omega
    rw [hsub, List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero] at ht
    have heval : (⟨before.length + 1 + middle.length, hindex⟩ : Fin m) = j := Fin.ext hm
    simpa only [heval, Option.some.injEq] using ht.symm
  exact ⟨before, middle, after, by simpa only [hx, hy] using he, hb, hm⟩

/-- 概要：実際の Schedule の行長移動は指定された二行だけを変更する（BF §1.4.4）。
方針：二行の set を同じ分割の位置で評価する。
規約：元の分割の長さと二行の順序は呼び出し側が指定する。
使われ方：三部分の抽出比較の変更後の行リストを実際の Schedule と同定する。 -/
lemma rows_transfer_blocks {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (donor receiver : Fin (d + 1)) (hne : donor ≠ receiver) (hd : 1 < (r.val donor).val)
    (before middle after : List (List (Fin n) × ℕ))
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = before ++
      (List.ofFn (fun k => (w receiver)⁻¹ k), (r.val receiver).val) ::
        (middle ++ (List.ofFn (fun k => (w donor)⁻¹ k), (r.val donor).val) :: after))
    (hr : before.length = receiver.val)
    (hm : before.length + 1 + middle.length = donor.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver hne hd) = before ++
      (List.ofFn (fun k => (w receiver)⁻¹ k), (r.val receiver).val + 1) ::
        (middle ++ (List.ofFn (fun k => (w donor)⁻¹ k), (r.val donor).val - 1) :: after) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_deletionScheduleTransfer, he, ← hr, ← hm]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.set_two_row_blocks before middle after _ _ _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
