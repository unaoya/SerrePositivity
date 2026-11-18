module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Words
public import Mathlib.GroupTheory.Perm.Basic

/-!
模型。文献の定義との比較は後で
# 全射語の値の置換

概要：Berger–Fresse §1.2.1 の対称群作用を非退化な全射語上に構成する。
方針：値の置換を全ての文字へ後合成する。
規約：これは共変な左作用で、置換の積は関数合成の順。
使われ方：χ の対称列と TR の同変性を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {n l : ℕ}

/-- 概要：値の置換は全射性を保ち、反映する（BF §1.2.1）。
方針：置換の全射性と単射性を使う。
規約：非退化性のない語にも適用する。
使われ方：非全射な語を零へ送る操作の同変性を示す。 -/
lemma surjective_rename_iff (σ : Equiv.Perm (Fin n)) (u : Fin l → Fin n) :
    Function.Surjective (σ ∘ u) ↔ Function.Surjective u := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h (σ k)
    exact ⟨i, σ.injective hi⟩
  · intro h
    exact σ.surjective.comp h

/-- 概要：値の置換は非退化性を保ち、反映する（BF §1.2.1）。
方針：文字の一致を置換の単射性で比較する。
規約：全射性のない語にも適用する。
使われ方：退化な語を零へ送る操作の同変性を示す。 -/
lemma nondegenerate_rename_iff (σ : Equiv.Perm (Fin n)) (u : Fin l → Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (σ ∘ u) ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate u := by
  constructor
  · intro h i j hij heq
    exact h i j hij (congrArg σ heq)
  · intro h i j hij heq
    exact h i j hij (σ.injective heq)

namespace Word

/-- 概要：値の置換は非退化全射語を非退化全射語へ送る（BF §1.2.1）。
方針：全射性は全単射との合成、非退化性は単射性で保たれる。
規約：語の位置と長さは保つ。
使われ方：対称群の左作用の対象上の写像となる。 -/
def rename (σ : Equiv.Perm (Fin n)) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l :=
  ⟨σ ∘ u.val, σ.surjective.comp u.surjective,
    fun i j h hij => u.nondegenerate i j h (σ.injective hij)⟩

/-- 概要：値の置換を文字ごとに評価する（BF §1.2.1）。
方針：後合成の定義を評価する。
規約：位置は固定する。
使われ方：削除と置換の可換性を計算する。 -/
@[simp]
lemma rename_apply (σ : Equiv.Perm (Fin n)) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (i : Fin l) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ u).val i = σ (u.val i) := rfl

/-- 概要：単位置換は全射語を保つ（BF §1.2.1）。
方針：各文字で比較する。
規約：共変な左作用。
使われ方：対称群作用の単位則を与える。 -/
@[simp]
lemma rename_one (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename 1 u = u := by
  apply Subtype.ext
  rfl

/-- 概要：値の置換は置換の積を保つ（BF §1.2.1）。
方針：後合成の結合則を評価する。
規約：σ*τ は先に τ、次に σ を適用する。
使われ方：対称群作用の合成則を与える。 -/
lemma rename_mul (σ τ : Equiv.Perm (Fin n)) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename (σ * τ) u = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename τ u) := by
  apply Subtype.ext
  rfl

/-- 概要：値の置換は全射語の型の同値を与える（BF §1.2.1）。
方針：逆置換を後合成する。
規約：同じ arity と長さの語を比較する。
使われ方：自由加群の基底の置換へ移す。 -/
def renameEquiv (σ : Equiv.Perm (Fin n)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l where
  toFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ
  invFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ.symm
  left_inv u := by apply Subtype.ext; funext i; simp
  right_inv u := by apply Subtype.ext; funext i; simp

end Word

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
