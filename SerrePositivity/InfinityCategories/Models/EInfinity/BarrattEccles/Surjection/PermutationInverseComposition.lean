module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationCompositionValues

/-!
模型。文献の定義との比較は後で
# 置換の部分合成の逆置換値

概要：Berger–Fresse §1.5.7 の合成 table の一行を内側・残りの外側のラベルで計算する。
方針：既存の順方向の部分合成値に逆置換を適用する。
規約：原典の語に対応するのは既存 BE 置換の逆置換。
使われ方：実際の逆置換行と部分語代入の一致を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：逆部分合成の外側ラベルの値（BF §1.5.7）。
方針：元の残りラベルの部分合成式を逆置換で消去する。
規約：出力側では σ(k) を除いた位置で読む。
使われ方：合成 table の外側由来の文字を照合する。 -/
lemma permutationComposition_inv_remaining (m n : ℕ) (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (a : {a : Fin (m + 1) // a ≠ σ k}) :
    (permutationComposition m n k σ τ)⁻¹ (remainingPosition m n (σ k) a) =
      remainingPosition m n k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv m k σ).symm a) := by
  have h := permutationComposition_remaining m n k σ τ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv m k σ).symm a)
  rw [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv m k σ).apply_symm_apply] at h
  rw [← h]
  exact (permutationComposition m n k σ τ).symm_apply_apply _

/-- 概要：逆部分合成の内側ラベルの値（BF §1.5.7）。
方針：内側逆置換の像を順方向の内部入力の式へ代入する。
規約：内側 arity 零では入力がなく矛盾なく成立する。
使われ方：合成 table の内側由来の文字を照合する。 -/
lemma permutationComposition_inv_inside (m n : ℕ) (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (a : Fin n) :
    (permutationComposition m n k σ τ)⁻¹ (insertedPosition m n (σ k) a) =
      insertedPosition m n k (τ⁻¹ a) := by
  have h := permutationComposition_inside m n k σ τ (τ⁻¹ a)
  have hτ : τ (τ⁻¹ a) = a := τ.apply_symm_apply a
  rw [hτ] at h
  rw [← h]
  exact (permutationComposition m n k σ τ).symm_apply_apply _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
