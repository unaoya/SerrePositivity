module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullaryAvailable
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseExtraction

/-!
模型。文献の定義との比較は後で
# 空語合成表の成功を早期除外した元の表へ戻す

概要：Berger–Fresse §1.5.7–9 の nullary 合成で実際の成功表を元の置換行へ戻す。
方針：指定値を初めから除外し、全抽出の削除公式と既存の解放値探索を使う。
規約：目標 Schedule はそのまま元の行の選択長とし、延長する一行を探索で得る。
使われ方：次数零の空語挿入の合成保存に必要な逆向き成功の構成。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：削除後の Schedule の行長を元の逆置換行に戻す（BF §1.5.7）。
方針：行の文字だけを元に戻し、選択長は変更しない。
規約：この段階では元の arity の Schedule とは主張しない。
使われ方：指定値を早期除外した成功表を構成する。 -/
def nullarySourceRows {m d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 0) d) : List (List (Fin (m + 1)) × ℕ) :=
  List.ofFn (fun i => (List.ofFn (w i).symm, (r.val i).val))

/-- 概要：実際の nullary 合成行は元の行の指定値削除（BF §1.5.7）。
方針：各逆置換行の既存の削除公式を有限列全体に適用する。
規約：全頂点で同じ空集合上の置換を使う。
使われ方：成功する Schedule ごとに表全体の削除公式を適用する。 -/
lemma rows_nullary {m d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (τ : Equiv.Perm (Fin 0)) (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 0) d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m 0 k (w j) τ) r =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r).map (fun p => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k p.1, p.2)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows, List.map_ofFn]
  congr 1
  funext i
  congr 1
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inverse_row_nullary (w i) τ k

/-- 概要：nullary 合成の全抽出は元の表で指定値を初めから除外した抽出の削除（BF §1.5.7）。
方針：各行の削除表示と全抽出の部分単射公式を連結する。
規約：失敗する Schedule も含む。
使われ方：合成表の成功を解放値探索の入力へ変換する。 -/
lemma reduceRows_nullary {m d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (τ : Equiv.Perm (Fin 0)) (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 0) d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m 0 k (w j) τ) r) [] =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r) [k]).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_nullary]
  simpa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_eraseSlotWord_of_mem k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r) [k] (by simp)

/-- 概要：削除前の行は解放値探索の完全行条件を満たす（BF §1.5.7）。
方針：逆置換行の非重複性と全値の被覆、目標 Schedule の正値性を使う。
規約：選択長の総和は削除後の arity に対応する。
使われ方：既存の逆向き解放値探索を実際の元の行へ適用する。 -/
lemma completeRows_nullarySourceRows {m d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 0) d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r) := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow_nodup w i, List.length_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.mem_vertexRow w i, r.property.1 i⟩

/-- 概要：実際の nullary 成功表から指定値を一回挿入した元の成功表を構成（BF §1.5.7–9）。
方針：早期除外表の成功を取り出し、既存の解放値探索で一行だけを延長する。
規約：元の表の成功や変更行の存在は仮定しない。Schedule への包装は別に行う。
使われ方：空語挿入の逆向きの成功項を具体的に得る。 -/
lemma nullary_success_extension {m d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 0) d) (out : List (Fin (m + 0)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m 0 k (w j) τ) r) [] =
      some out) :
    ∃ before chosen after pre post,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r = before ++ chosen :: after ∧
      k ∉ pre ∧ k ∉ post ∧ out = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (pre ++ post) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (chosen.1, chosen.2 + 1) :: after) [] =
        some (pre ++ k :: post) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_nullary] at h
  cases he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r) [k] with
  | none => simp [he] at h
  | some raw =>
    have hout : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k raw = out := by simpa only [he, Option.map_some,
      Option.some.injEq] using h
    have hne : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r ≠ [] := by
      intro hz
      have hl : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r).length = d + 1 := List.length_ofFn
      rw [hz] at hl
      simp at hl
    have hb : ([] : List (Fin (m + 1))).length + 1 +
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r).map (fun p => p.2 - 1)).sum + 1 = m + 1 := by
      have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_excess_sum r
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
        List.length_nil, Nat.zero_add, Nat.add_zero] at hs ⊢
      omega
    obtain ⟨before, picked, finish, chosen, after, pre, post, hs, _, _, hr, hp, hpost, hh⟩ :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.releaseSearch_constructs_extension (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r) [] k raw hne
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.completeRows_nullarySourceRows w r) (by simp) (by simp) he hb
    exact ⟨before, chosen, after, pre, post, hs.decomposition, hp, hpost,
      hout.symm.trans (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k) hr), hh⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
