module
public import SerrePositivity.KST.ProExcision.BlockColumnCommute
public import SerrePositivity.KST.ProExcision.GroupProductData

/-!
# 補助列の群準同型と μ の積の構成

概要：補助列 ψ は列ベクトルの加法群から行列単位群への準同型であり、可換な二つの像から μ を作る。
方針：二つの補助列の交差積を零と証明し、1+V の積を加法に直す。
規約：KST Lemma 4.16 の非可換版と Construction A.5 の明示的な μ。
使われ方：P のブロック埋め込みと ψ(Q) の実準同型を μ:P×Q→H に束ねる。
-/
@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]
variable {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- 概要：同じ補助列に入る二つの列行列の積は零。
方針：列の添字が元の全ての行の添字と異なることを各積に使う。
規約：KST Lemma 4.16、二つのベクトルは独立。
使われ方：ψ の乗法保存と可換性。 -/
lemma blockColumn_mul_zero (r : ι → κ) (p : κ) (v w : ι → R)
    (hp : ∀ i, p ≠ r i) : blockColumn r p v * blockColumn r p w = 0 := by
  simp only [blockColumn, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  exact @Matrix.single_mul_single_of_ne κ κ κ R _ _ _ _ _ (v j) (r j) p (r i) p (hp i) (w i)

/-- 概要：補助列行列は列ベクトルの加法を保つ。
方針：単一成分行列と有限和の加法性を使う。
規約：KST 4.16。使われ方：ψ の準同型性。 -/
lemma blockColumn_add (r : ι → κ) (p : κ) (v w : ι → R) :
    blockColumn r p (v + w) = blockColumn r p v + blockColumn r p w := by
  simp only [blockColumn, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]

/-- 概要：列ベクトルの加法群を 1+V として行列の単位群へ埋める準同型。
方針：二乗零の単位と、独立な二つの列の交差積の消滅を使う。
規約：KST Lemma 4.16 の ψ、非可換係数でも成立する。
使われ方：μ の第二因子 Q の実群準同型。 -/
def blockColumnHom (r : ι → κ) (p : κ) (hp : ∀ i, p ≠ r i) :
    Multiplicative (ι → R) →* (Matrix κ κ R)ˣ where
  toFun v := squareZeroUnit (blockColumn r p v.toAdd) (blockColumn_square_zero r p v.toAdd hp)
  map_one' := by
    apply Units.ext
    change 1 + blockColumn r p 0 = 1
    simp only [blockColumn, Pi.zero_apply, Matrix.single_zero, Finset.sum_const_zero, add_zero]
  map_mul' v w := by
    apply Units.ext
    change 1 + blockColumn r p (v.toAdd + w.toAdd) =
      (1 + blockColumn r p v.toAdd) * (1 + blockColumn r p w.toAdd)
    rw [blockColumn_add, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul,
      blockColumn_mul_zero r p v.toAdd w.toAdd hp, add_zero]
    abel

/-- 概要：二つの群準同型の像の可換性から直積上の実準同型 μ を構成する。
方針：第一因子と第二因子の像の積を取り、交差項だけを可換にする。
規約：KST A.5 の μ と Lemma 4.16 の P,Q,H を明示する方式。
使われ方：ブロック P の埋め込みと ψ の準同型を最後の μ に束ねる。 -/
def commutingProductHom {P Q H : Type u} [Group P] [Group Q] [Group H]
    (f : P →* H) (g : Q →* H) (h : ∀ p q, Commute (f p) (g q)) : P × Q →* H where
  toFun z := f z.1 * g z.2
  map_one' := by
    change f 1 * g 1 = 1
    rw [map_one, map_one, mul_one]
  map_mul' z z' := by
    change f (z.1 * z'.1) * g (z.2 * z'.2) = (f z.1 * g z.2) * (f z'.1 * g z'.2)
    rw [map_mul, map_mul]
    calc
      _ = f z.1 * (f z'.1 * g z.2) * g z'.2 := by simp only [mul_assoc]
      _ = f z.1 * (g z.2 * f z'.1) * g z'.2 := by rw [(h z'.1 z.2).eq]
      _ = _ := by simp only [mul_assoc]

end SerrePositivity.KST.ProExcision
