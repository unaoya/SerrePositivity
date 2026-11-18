module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix

/-!
模型。文献の定義との比較は後で
# 既存の先行抽出証跡に沿った成功の分割

概要：Berger–Fresse §1.4.4 の変更後の成功を指定済みの先行状態で切る。
方針：同じ再帰の先行証跡で帰納して後続の成功と出力を取り出す。
規約：証跡と別の分割の状態の一致を追加仮定しない。
使われ方：逆探索の停止行で実際に選択される値を全出力へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：成功抽出は既存の先行証跡の終端状態で分割できる（BF §1.4.4）。
方針：一行の成功を開いて証跡の後続に帰納法を適用する。
規約：後続の成功と先行語の等式をともに保持する。
使われ方：変更後の成功の停止行の状態を逆探索の状態と厳密に揃える。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.split_success {α : Type*} [DecidableEq α]
    {before : List (List α × ℕ)} {removed finish : List α} {picked : List (List α)}
    (hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish)
    (rest : List (List α × ℕ)) (out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ rest) removed = some out) :
    ∃ tail, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest finish = some tail ∧ out = picked.flatten ++ tail := by
  induction hp generalizing out with
  | nil => exact ⟨out, h, by simp⟩
  | cons hr hb hp ih =>
    obtain ⟨_, _, tail, ht, hout⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
    obtain ⟨post, hpost, he⟩ := ih tail ht
    refine ⟨post, hpost, ?_⟩
    rw [hout, he, List.flatten_cons, List.append_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
