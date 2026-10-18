module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Field.Rat

/-!
# (3.8) の置換不変部分

## 概要
推移的な G 集合上の積において、置換作用の不変部分は定数族である。

## 方針
二つの添字を結ぶ群元を選び、固定条件を評価する。

## 規約
これは通常の不変部分の計算。hG の実構成や π_n(hG) との比較は含まない。
この計算自体には群や添字の有限性も不要。

## 使われ方
論文 定理 3.1 の証明中の (3.8)、有理 Shapiro の π_* 側の置換作用の部分。
-/

@[expose] public section

namespace SerrePositivity.KST.Descent

variable (G I M : Type*) [Group G] [MulAction G I] [AddCommGroup M] [Module ℚ M]

/-- 概要：積の置換作用で固定される族（論文 (3.8)）。
方針：`v (g • i) = v i` を全添字で要求し、部分加群として束ねる。
規約：通常の左作用の逆元による置換と同じ固定条件。
使われ方：section の G 軌道に添字を持つ積の不変部分。 -/
def permutationInvariants : Submodule ℚ (I → M) where
  carrier := {v | ∀ (g : G) (i : I), v (g • i) = v i}
  zero_mem' _ _ := rfl
  add_mem' hv hw g i := by simp only [Pi.add_apply, hv g i, hw g i]
  smul_mem' a v hv g i := by simp only [Pi.smul_apply, hv g i]

/-- 概要：推移的作用の不変族は定数族（論文 (3.8)）。
方針：二点を結ぶ群元で固定条件を評価する。
規約：空集合上では点を選べないため、この命題は与えられた二点について述べる。
使われ方：評価写像の単射性と Shapiro の具体的な逆写像。 -/
theorem permutationInvariants_constant [MulAction.IsPretransitive G I]
    (v : permutationInvariants G I M) (i j : I) : v.val i = v.val j := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G j i
  simpa only [hg] using v.property g j

/-- 概要：非空な推移的 G 集合上の置換不変部分と元の加群の線形同型（論文 (3.8)）。
方針：指定した点で評価し、逆向きには定数族を取る。
規約：点 `i₀` を明示する。選択や有界性の仮定を不要にする。
使われ方：有理固定点と π_* の比較を別途適用した後の (3.8) の計算。 -/
def permutationInvariantsEquiv [MulAction.IsPretransitive G I] (i₀ : I) :
    permutationInvariants G I M ≃ₗ[ℚ] M where
  toFun v := v.val i₀
  invFun x := ⟨fun _ ↦ x, fun _ _ ↦ rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    exact permutationInvariants_constant G I M v i₀ i
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 概要：置換不変部分の評価は選んだ点に依存しない（論文 (3.8) の自然性）。
方針：不変族の定数性を使う。
規約：群作用の推移性が必要。
使われ方：section の代表の選択から最終比較が独立であることを確認する。 -/
theorem permutationInvariantsEquiv_apply_eq [MulAction.IsPretransitive G I]
    (i j : I) (v : permutationInvariants G I M) :
    permutationInvariantsEquiv G I M i v = permutationInvariantsEquiv G I M j v :=
  permutationInvariants_constant G I M v i j

end SerrePositivity.KST.Descent
