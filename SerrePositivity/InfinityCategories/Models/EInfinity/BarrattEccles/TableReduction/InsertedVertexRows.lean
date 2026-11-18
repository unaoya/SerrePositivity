module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonInsertion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonBoundary

/-!
模型。文献の定義との比較は後で
# 一文字行を復元した table の抽出成功

概要：Berger–Fresse §1.4.4 の頂点境界との対応を逆向きにも構成する。
方針：Schedule の除外予算が arity 未満であることから元の頂点行を挿入する。
規約：最終位置への挿入も許す。
使われ方：一文字行の table と頂点境界の table の成功・失敗を一致させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：頂点削除後の成功 table に元の一文字行を復元できる（BF §1.4.4）。
方針：削除された実際の行を元の位置に挿入する。
規約：出力の全射性や非退化性を仮定せず、位置と出力分割も保持する。
使われ方：頂点境界の各成功項から元の削除微分の項を構成する。 -/
lemma reduceRows_inserted_vertex {n d : ℕ} (w : Fin (d + 2) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1)) (i : Fin (d + 2)) (hi : (r.val i).val = 1)
    (out : List (Fin n))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)) [] =
      some out) :
    ∃ pre a post, out = pre ++ post ∧
      pre.length = ((List.ofFn (fun j => (r.val j).val)).take i.val).sum ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (pre ++ a :: post) := by
  have hib : i.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).length := by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn] using i.isLt
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).take i.val ++
      (List.ofFn (fun k => (w i)⁻¹ k), 1) :: (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop (i.val + 1) := by
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).take i.val ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop i.val :=
        (List.take_append_drop i.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r)).symm
      _ = _ := by
        rw [List.drop_eq_getElem_cons hib]
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.getElem_ofFn, Fin.eta, hi]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_scheduleDelete, List.eraseIdx_eq_take_drop_succ] at h
  have hn := List.nodup_ofFn_ofInjective (w i).symm.injective
  have hb : ([] : List (Fin n)).length +
      (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).take i.val).map (fun p => p.2 - 1)).sum <
        (List.ofFn (fun k => (w i)⁻¹ k)).length := by
    simpa only [List.length_nil, Nat.zero_add, List.length_ofFn] using
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_prefix_budget w r i.val
  obtain ⟨pre, a, post, hp, hl, hc⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_insert_singleton _ _ _ _ _ hn hb h
  refine ⟨pre, a, post, hp, ?_, ?_⟩
  · rw [List.map_take, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn] at hl
    exact hl
  · exact (congrArg (fun rs => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rs []) he).trans hc

/-- 概要：一文字行を持つ table の抽出成功と頂点削除後の成功は同値（BF §1.4.4）。
方針：行を削除する公式と挿入する公式を両方向に適用する。
規約：最終行を含み、出力が退化している場合も扱う。
使われ方：有限和の添字対応で無効な Schedule も正確に除外する。 -/
lemma singleton_reduction_success_iff {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (i : Fin (d + 2)) (hi : (r.val i).val = 1) :
    (∃ out, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) ↔
      ∃ out, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)) [] =
        some out := by
  constructor
  · rintro ⟨out, h⟩
    obtain ⟨pre, a, post, _, _, hc⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_deleted_vertex w r i hi out h
    exact ⟨pre ++ post, hc⟩
  · rintro ⟨out, h⟩
    obtain ⟨pre, a, post, _, _, hc⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_inserted_vertex w r i hi out h
    exact ⟨pre ++ a :: post, hc⟩

/-- 概要：元の table の失敗は頂点削除後の失敗と同値（BF §1.4.4）。
方針：Option が成功値を持つことの同値を否定する。
規約：正規化による零ではなく、行抽出そのものの失敗を扱う。
使われ方：一文字行の境界の有限和で失敗項を同時に零とする。 -/
lemma singleton_reduction_none_iff {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (i : Fin (d + 2)) (hi : (r.val i).val = 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = none ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)) [] = none := by
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singleton_reduction_success_iff w r i hi
  cases ho : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] <;>
    cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi)) [] <;>
    simp_all

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
