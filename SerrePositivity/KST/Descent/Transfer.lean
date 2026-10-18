module

public import SerrePositivity.KST.Descent.Axioms
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Tactic.NormNum

/-!
# 補題 3.2 の transfer の有理分裂

## 概要
有限平坦射のベクトル束を自明化した後の `trf ∘ f* = rank` から、自然な左逆を得る。

## 方針
正の rank を有理数として割る。自然性は transfer の自然性から独立に証明する。

## 規約
幾何学的な transfer の存在や大域的な rank 公式は仮定しない。
本ファイルは与えられた線形写像とその等式に対する代数的補題だけを証明する。

## 使われ方
論文 補題 3.2 の前層の retract を、Čech 図式上で構成するための部品。
これだけで Tot の降下を証明したとは主張しない。
-/

@[expose] public section

namespace SerrePositivity.KST.Descent

section

variable {M N M' N' : Type*}
variable [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
variable [AddCommGroup M'] [Module ℚ M'] [AddCommGroup N'] [Module ℚ N']

/-- 概要：rank で割った transfer（論文 補題 3.2）。
方針：有理線形写像に rank の逆数を掛ける。
規約：rank がゼロの場合にも写像は定義されるが、分裂には正値性が必要。
使われ方：ベクトル束を自明化した開集合上の前層の retraction。 -/
def normalizedTransfer (rank : ℕ) (transfer : N →ₗ[ℚ] M) : N →ₗ[ℚ] M :=
  (rank : ℚ)⁻¹ • transfer

/-- 概要：正の rank の合成公式から引き戻しの左逆を得る（論文 補題 3.2）。
方針：`trf ∘ f* = rank` を評価し、正の rank を有理数として消去する。
規約：合成公式は自明化したベクトル束に対する局所的な式として与える。
使われ方：Čech 比較の retract を構成する際の分裂恒等式。 -/
theorem normalizedTransfer_comp (rank : ℕ) (positive : 0 < rank)
    (pullback : M →ₗ[ℚ] N) (transfer : N →ₗ[ℚ] M)
    (rank_identity : transfer.comp pullback = (rank : ℚ) • LinearMap.id) :
    (normalizedTransfer rank transfer).comp pullback = LinearMap.id := by
  ext x
  have hx := LinearMap.congr_fun rank_identity x
  change transfer (pullback x) = (rank : ℚ) • x at hx
  change (rank : ℚ)⁻¹ • transfer (pullback x) = x
  rw [hx, smul_smul, inv_mul_cancel₀ (by exact_mod_cast positive.ne'), one_smul]

/-- 概要：正の rank の transfer 公式は引き戻しの単射性を与える（論文 補題 3.2）。
方針：正規化した transfer が左逆であることを使う。
規約：各次数の単射性は Čech 降下の完成とは区別する。
使われ方：全次数比較の代数的な検査と後の retract 議論。 -/
theorem pullback_injective_of_transfer (rank : ℕ) (positive : 0 < rank)
    (pullback : M →ₗ[ℚ] N) (transfer : N →ₗ[ℚ] M)
    (rank_identity : transfer.comp pullback = (rank : ℚ) • LinearMap.id) :
    Function.Injective pullback := by
  apply Function.LeftInverse.injective (g := normalizedTransfer rank transfer)
  intro x
  exact LinearMap.congr_fun
    (normalizedTransfer_comp rank positive pullback transfer rank_identity) x

/-- 概要：正規化した transfer は自然性の正方形を保つ（論文 補題 3.2）。
方針：与えられた transfer の可換式の両辺に同じ有理スカラーを掛ける。
規約：rank は一つの自明化から全図式に引き戻した共通の値。
使われ方：対象ごとの左逆を前層の自然な retraction として使う。 -/
theorem normalizedTransfer_naturality (rank : ℕ)
    (transfer : N →ₗ[ℚ] M) (transfer' : N' →ₗ[ℚ] M')
    (onSource : N →ₗ[ℚ] N') (onTarget : M →ₗ[ℚ] M')
    (naturality : onTarget.comp transfer = transfer'.comp onSource) :
    onTarget.comp (normalizedTransfer rank transfer) =
      (normalizedTransfer rank transfer').comp onSource := by
  ext x
  have hx := LinearMap.congr_fun naturality x
  simpa only [normalizedTransfer, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
    using congrArg (fun y ↦ (rank : ℚ)⁻¹ • y) hx

end

end SerrePositivity.KST.Descent
