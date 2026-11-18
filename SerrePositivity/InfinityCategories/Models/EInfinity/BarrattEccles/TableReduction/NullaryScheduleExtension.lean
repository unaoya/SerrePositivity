module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullaryEarlyExclusion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOfTable

/-!
模型。文献の定義との比較は後で
# 空語挿入の逆構成を元の Schedule にまとめる

概要：Berger–Fresse §1.5.7–9 の nullary 成功から元の次数の成功 Schedule を構成する。
方針：一行延長で逆置換行列は不変、選択長総和は一増えるので既存の包装を適用する。
規約：延長行の存在と成功は解放値探索から得て、入力には要求しない。
使われ方：実際の空語合成の成功項を元の TR の成功項へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：元の行へ戻した削除表の選択長総和は削除後の arity と次数の和（BF §1.5.7）。
方針：有限列の和を Schedule の総和へ移す。
規約：成功を仮定しない。
使われ方：一行延長後の表の次数を元の arity で固定する。 -/
lemma nullarySourceRows_sum {m d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 0) d) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows w r).map Prod.snd).sum = m + d := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    Nat.add_zero] using r.property.2

/-- 概要：nullary の実際の成功から元の Schedule と指定値一回の成功語を構成（BF §1.5.7–9）。
方針：解放値探索で一行を延長し、同じ逆行列と一増えた総和から Schedule に包装する。
規約：削除後の語の非退化性はまだ要求しない。
使われ方：全成功基底語の逆対応を構成する入力。 -/
lemma nullary_success_schedule {m d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 0) d) (out : List (Fin (m + 0)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m 0 k (w j) τ) r) [] =
      some out) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d, ∃ pre post,
      k ∉ pre ∧ k ∉ post ∧ out = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (pre ++ post) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (pre ++ k :: post) := by
  obtain ⟨before, chosen, after, pre, post, he, hp, hpost, ho, hh⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullary_success_extension w τ k r out h
  have hm : (before ++ (chosen.1, chosen.2 + 1) :: after).map Prod.fst =
      List.ofFn (fun i => List.ofFn (w i).symm) := by
    have he' := congrArg (List.map Prod.fst) he
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows, List.map_ofFn, List.map_append, List.map_cons,
      Function.comp_def] using he'.symm
  have ht : ((before ++ (chosen.1, chosen.2 + 1) :: after).map Prod.snd).sum =
      m + 1 + d := by
    have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceRows_sum w r
    rw [he] at hs
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hs ⊢
    omega
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_of_table w _ _ hh hm ht
  exact ⟨s, pre, post, hp, hpost, ho, by rw [hs]; exact hh⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
