module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransferBounds

/-!
模型。文献の定義との比較は後で
# 行長移動による実際の table の二行の更新

概要：Berger–Fresse §1.4.4 の Schedule の移動を実際の行リストの変更へ移す。
方針：有限関数の更新をリストの set と比較し、二行以外が変わらないことを使う。
規約：置換列は同じままで行長だけを変更する。
使われ方：三部分の抽出比較を実際の相殺相手の Schedule へ適用する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：有限関数の一成分の更新はリストの同じ位置の更新（BF §1.4.4）。
方針：全位置で getElem を比較する。
規約：更新位置は有限添字で指定する。
使われ方：行長関数の変更を実際の table のリストへ直す。 -/
lemma ofFn_update_eq_set {α : Type*} {m : ℕ} (f : Fin m → α) (i : Fin m) (a : α) :
    List.ofFn (Function.update f i a) = (List.ofFn f).set i.val a := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp only [List.length_ofFn] at hk
  rw [List.getElem_ofFn, List.getElem_set, List.getElem_ofFn]
  by_cases hi : i.val = k
  · have he : (⟨k, hk⟩ : Fin m) = i := Fin.ext hi.symm
    simp only [he, Function.update_self, hi, ↓reduceIte]
  · have he : (⟨k, hk⟩ : Fin m) ≠ i := fun h => hi (congrArg Fin.val h).symm
    simp only [Function.update_of_ne he, hi, ↓reduceIte]

/-- 概要：行長を移した Schedule の行リストは二つの set で得られる（BF §1.4.4）。
方針：二つの有限関数の更新を各行の対へ移す。
規約：先に削除行を短くし、次に受け取り行を長くする。
使われ方：元と相殺相手の table を同じ前・中・後の分割で表示する。 -/
lemma rows_deletionScheduleTransfer {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (donor receiver : Fin (d + 1)) (hne : donor ≠ receiver)
    (hd : 1 < (r.val donor).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver hne hd) =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).set donor.val
        (List.ofFn (fun k => (w donor)⁻¹ k), (r.val donor).val - 1)).set receiver.val
          (List.ofFn (fun k => (w receiver)⁻¹ k), (r.val receiver).val + 1) := by
  let f := fun i => (List.ofFn (fun k => (w i)⁻¹ k), (r.val i).val)
  have he : (fun i => (List.ofFn (fun k => (w i)⁻¹ k),
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver hne hd).val i).val)) =
        Function.update (Function.update f donor
          (List.ofFn (fun k => (w donor)⁻¹ k), (r.val donor).val - 1)) receiver
          (List.ofFn (fun k => (w receiver)⁻¹ k), (r.val receiver).val + 1) := by
    funext i
    by_cases hir : i = receiver
    · subst i
      simp only [Function.update_self, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_receiver]
    · by_cases hid : i = donor
      · subst i
        simp only [Function.update_of_ne hne, Function.update_self,
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_donor]
      · rw [Function.update_of_ne hir, Function.update_of_ne hid]
        change (List.ofFn (fun k => (w i)⁻¹ k),
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver hne hd).val i).val) =
            (List.ofFn (fun k => (w i)⁻¹ k), (r.val i).val)
        congr 1
        exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_other _ donor receiver i hid hir
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows
  rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ofFn_update_eq_set, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ofFn_update_eq_set]

/-- 概要：前・中・後で分割した二行の更新は同じ分割を保つ（BF §1.4.4）。
方針：set を連結リストの指定位置へ移す。
規約：先の行と後の行は一つ以上離れている。
使われ方：Schedule の二つの set を三部分の抽出比較の入力へ変える。 -/
lemma set_two_row_blocks {α : Type*} (before middle after : List α) (x y x' y' : α) :
    (((before ++ x :: (middle ++ y :: after)).set
      (before.length + 1 + middle.length) y').set before.length x') =
        before ++ x' :: (middle ++ y' :: after) := by
  rw [List.set_append_right _ _ (by omega)]
  have he : before.length + 1 + middle.length - before.length = middle.length + 1 := by omega
  rw [he, List.set_cons_succ, List.set_append_right _ _ (by omega), Nat.sub_self]
  simp only [List.set_cons_zero]
  rw [List.set_append_right _ _ (by omega), Nat.sub_self, List.set_cons_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
