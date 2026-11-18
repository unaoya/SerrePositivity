module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Renaming

/-!
模型。文献の定義との比較は後で
# 次数零の全射語と置換

概要：Berger–Fresse §1.2.1・§1.3.1 の次数零の基底を置換と同定する。
方針：同じ有限濃度での全射を全単射にする。
規約：既存 BE の右乗法の規約との比較には逆置換の一行表示を使う。
使われ方：一般の TR の次数零の式と対称群の規約を固定する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：置換の一行表示は次数零の非退化全射語（BF §1.2.1）。
方針：全単射の単射性から非退化性を得る。
規約：文字列の値は σ(i)。
使われ方：次数零の基底の同定の逆写像となる。 -/
def permutationWord {n : ℕ} (σ : Equiv.Perm (Fin n)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0 :=
  ⟨σ, σ.surjective, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.nondegenerate_of_injective σ.injective⟩

/-- 概要：次数零の非退化全射語は置換と一対一に対応する（BF §1.2.1）。
方針：有限集合の自己全射の単射性を用いる。
規約：arity 0 の空置換も含む。
使われ方：TR の次数零の同定と nullary 成分を検証する。 -/
def degreeZeroEquiv (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0 ≃ Equiv.Perm (Fin n) where
  toFun u := Equiv.ofBijective u.val
    ⟨Finite.injective_iff_surjective.2 u.surjective, u.surjective⟩
  invFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord
  left_inv u := by apply Subtype.ext; rfl
  right_inv σ := by ext i; rfl

/-- 概要：次数零の語の置換対応は文字ごとの値を保つ（BF §1.2.1）。
方針：同値の定義を評価する。
規約：一行表示をそのまま置換に戻す。
使われ方：table reduction の一行の計算を簡約する。 -/
@[simp]
lemma degreeZeroEquiv_apply {n : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeZeroEquiv n u i = u.val i := rfl

/-- 概要：値の置換は次数零で置換の左乗法になる（BF §1.2.1）。
方針：全ての文字で評価して比較する。
規約：左から値を置換する作用。
使われ方：χ の対称列の規約を検証する。 -/
lemma degreeZeroEquiv_rename {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeZeroEquiv n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ u) = σ * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeZeroEquiv n u := by
  ext i
  rfl

/-- 概要：既存 BE の置換から対応する一行表示の語を作る（BF §1.3.1）。
方針：位置の置換として持つ BE の置換を逆にして値の列へ直す。
規約：BE の対称列は逆置換の右乗法で共変に作用する。
使われ方：table reduction の入力の各行に同じ規約を適用する。 -/
def barrattEcclesWord {n : ℕ} (σ : Equiv.Perm (Fin n)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0 :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord σ⁻¹

/-- 概要：BE の逆置換の右乗法は語の値の左作用になる（BF §1.3.1）。
方針：積の逆元の公式を各文字で評価する。
規約：既存 BE の対称列の作用と同じ σ⁻¹ の右乗法を使う。
使われ方：一般の TR の同変性の次数零の比較となる。 -/
lemma barrattEcclesWord_action {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.barrattEcclesWord (σ * τ⁻¹) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename τ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.barrattEcclesWord σ) := by
  apply Subtype.ext
  funext i
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.barrattEcclesWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename, mul_inv_rev]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
