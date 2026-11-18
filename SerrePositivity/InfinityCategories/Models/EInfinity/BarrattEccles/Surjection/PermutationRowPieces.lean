module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationInverseComposition
public import Mathlib.Data.List.OfFn

/-!
模型。文献の定義との比較は後で
# 逆置換行の指定値の前後の部分

概要：Berger–Fresse §1.5.7 の外側逆置換行を指定値 k の前後で分割する。
方針：k の出現位置 σ(k) より前と後の有限位置で逆置換を評価する。
規約：両部分の文字は k と異なる証明を保持する。
使われ方：合成置換行を外側前半・内側行・外側後半へ記述する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：逆置換行の k の前の文字列（BF §1.5.7）。
方針：出力位置 σ(k) より前の位置で逆置換を評価する。
規約：値の型から k を除く。
使われ方：合成行の挿入ブロックより前の部分。 -/
def permutationBefore {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1)) :
    List {a : Fin (m + 1) // a ≠ k} :=
  List.ofFn (fun j : Fin (σ k).val =>
    ⟨σ.symm ⟨j.val, by have := (σ k).isLt; omega⟩, by
      intro h
      have hv := congrArg (fun a => (σ a).val) h
      simp only [Equiv.apply_symm_apply] at hv
      have := j.isLt
      omega⟩)

/-- 概要：逆置換行の k の後の文字列（BF §1.5.7）。
方針：出力位置 σ(k) の次から最後まで逆置換を評価する。
規約：値の型から k を除く。
使われ方：合成行の挿入ブロックより後の部分。 -/
def permutationAfter {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1)) :
    List {a : Fin (m + 1) // a ≠ k} :=
  List.ofFn (fun j : Fin (m - (σ k).val) =>
    ⟨σ.symm ⟨(σ k).val + 1 + j.val, by have := j.isLt; have := (σ k).isLt; omega⟩, by
      intro h
      have hv := congrArg (fun a => (σ a).val) h
      simp only [Equiv.apply_symm_apply] at hv
      omega⟩)

/-- 概要：前半の長さは k の出現位置（BF §1.5.7）。
方針：ofFn の長さを計算する。
規約：位置は零始まり。
使われ方：行の連結の添字を分ける。 -/
@[simp] lemma permutationBefore_length {m : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 1)) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).length = (σ k).val := List.length_ofFn

/-- 概要：後半の長さは全長から指定位置と一文字を除いたもの（BF §1.5.7）。
方針：ofFn の長さを計算する。
規約：後半が空でもよい。
使われ方：合成行の全長を検証する。 -/
@[simp] lemma permutationAfter_length {m : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 1)) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).length = m - (σ k).val := List.length_ofFn

/-- 概要：前半の j 文字目の σ による像は元の位置 j（BF §1.5.7）。
方針：ofFn の評価と置換・逆置換の消去を使う。
規約：前半の有限添字の自然数値で述べる。
使われ方：合成置換の前半の値を全体の位置へ戻す。 -/
lemma permutationBefore_get_apply {m : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 1)) (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).length) :
    (σ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k)[j.val]).val).val = j.val := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore, List.getElem_ofFn, Equiv.apply_symm_apply]

/-- 概要：後半の j 文字目の σ による像は指定位置の次から数えた位置（BF §1.5.7）。
方針：ofFn の評価と置換・逆置換の消去を使う。
規約：後半の有限添字は零始まり。
使われ方：合成置換の後半の値を全体の位置へ戻す。 -/
lemma permutationAfter_get_apply {m : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 1)) (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).length) :
    (σ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k)[j.val]).val).val = (σ k).val + 1 + j.val := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter, List.getElem_ofFn, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
