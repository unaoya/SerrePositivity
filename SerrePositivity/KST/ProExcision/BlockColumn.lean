module
public import SerrePositivity.KST.ProExcision.BlockConjugation
public import Mathlib.Data.Matrix.Basis

/-!
# Lemma 4.16 の補助列の実行列

概要：指定した行と一つの補助列にベクトルを入れ、零積と右乗法の公式を証明する。
方針：行列の単一成分行列の有限和を使う。
規約：KST Lemma 4.16 の非可換再記述。補助行 p と最後の列 q を区別する。
使われ方：共役公式 u⁻¹ψ(v)u=ψ(v)φ(v) の非可換な実行列への適用。
-/
@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]
variable {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- 概要：指定した行と一列にベクトルを入れる行列。
方針：単一成分行列を有限和で足す。
規約：KST Lemma 4.16 の ψ の非自明な成分。
使われ方：補助列と右乗法の具体的な行列模型。 -/
def blockColumn (r : ι → κ) (p : κ) (v : ι → R) : Matrix κ κ R :=
  ∑ i, Matrix.single (r i) p (v i)

/-- 概要：補助列の行にベクトルの行が無ければ列行列の二乗は零。
方針：二重和の各単一成分行列の積を零にする。
規約：KST 4.16、可換性不要。使われ方：ψ(v) の単位の逆。 -/
lemma blockColumn_square_zero (r : ι → κ) (p : κ) (v : ι → R)
    (hp : ∀ i, p ≠ r i) : blockColumn r p v * blockColumn r p v = 0 := by
  simp only [blockColumn, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  exact @Matrix.single_mul_single_of_ne κ κ κ R _ _ _ _ _ (v j) (r j) p (r i) p (hp i) (v i)

/-- 概要：補助行から最後の列への行列を右から掛けると列ベクトルの右乗法になる。
方針：共有する補助列・行の成分だけが積に残る。
規約：KST 4.16、積 v_i a の順序を固定する。
使われ方：VU を φ(v) の非自明な列へ同定する。 -/
lemma blockColumn_mul_aux (r : ι → κ) (p q : κ) (v : ι → R) (a : R) :
    blockColumn r p v * Matrix.single p q a = blockColumn r q (fun i ↦ v i * a) := by
  simp only [blockColumn, Finset.sum_mul, Matrix.single_mul_single_same]

/-- 概要：最後の列が元の行と交わらなければ逆順の積は零。
方針：単一成分行列の積の中間添字が一致しないことを使う。
規約：KST 4.16 の UV=0。使われ方：補助元による非可換共役公式。 -/
lemma aux_mul_blockColumn_zero (r : ι → κ) (p q : κ) (v : ι → R) (a : R)
    (hq : ∀ i, q ≠ r i) : Matrix.single p q a * blockColumn r p v = 0 := by
  simp only [blockColumn, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact @Matrix.single_mul_single_of_ne κ κ κ R _ _ _ _ _ a p q (r i) p (hq i) (v i)

/-- 概要：実行列の補助元による共役が右乗法の列を付け加える。
方針：U²=V²=UV=0 と VU の実列公式を一般の零積共役公式へ代入する。
規約：KST Lemma 4.16 の非可換再記述、I の単位化にも適用できる。
使われ方：A.6 の共役比較と μ 版 A.5 の積の端点の同定。 -/
lemma blockColumn_conjugation (r : ι → κ) (p q : κ) (v : ι → R) (a : R)
    (hpq : q ≠ p) (hp : ∀ i, p ≠ r i) (hq : ∀ i, q ≠ r i) :
    (1 - Matrix.single p q a) * (1 + blockColumn r p v) * (1 + Matrix.single p q a) =
      (1 + blockColumn r p v) * (1 + blockColumn r q (fun i ↦ v i * a)) := by
  have hU : Matrix.single p q a * Matrix.single p q a = 0 :=
    @Matrix.single_mul_single_of_ne κ κ κ R _ _ _ _ _ a p q p q hpq a
  have h := squareZero_conjugation (Matrix.single p q a) (blockColumn r p v) hU
    (blockColumn_square_zero r p v hp) (aux_mul_blockColumn_zero r p q v a hq)
  rw [blockColumn_mul_aux] at h
  exact h

end SerrePositivity.KST.ProExcision
