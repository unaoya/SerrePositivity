module
public import SerrePositivity.KST.ProExcision.FirstBlockMatrix

/-!
# 安定一般線形作用のための Whitehead ブロック分解

概要：diag(g,g⁻¹) を六つの上・下ブロック単冪行列の積へ実分解する。
方針：ブロック積を非可換な環で直接計算する。
規約：KST Proposition 4.14、SW92 Proposition 1.5 の生成系の文言と異なる再構成の経路。
使われ方：整数 GL の作用を有限支持と elementary 行列の作用へ帰着する。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- 概要：上ブロック単冪行列の実単位。
方針：逆の非対角ブロックを −A とする。
規約：SW92 Proposition 1.5 の作用の再構成。使われ方：Whitehead 分解の因子。 -/
def blockUpperUnit (A : Matrix ι ι R) : (Matrix (ι ⊕ ι) (ι ⊕ ι) R)ˣ where
  val := Matrix.fromBlocks 1 A 0 1
  inv := Matrix.fromBlocks 1 (-A) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

/-- 概要：下ブロック単冪行列の実単位。
方針：逆の非対角ブロックを −A とする。
規約：SW92 Proposition 1.5 の作用の再構成。使われ方：Whitehead 分解の因子。 -/
def blockLowerUnit (A : Matrix ι ι R) : (Matrix (ι ⊕ ι) (ι ⊕ ι) R)ˣ where
  val := Matrix.fromBlocks 1 0 A 1
  inv := Matrix.fromBlocks 1 0 (-A) 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

/-- 概要：diag(g,g⁻¹) の六つのブロック単冪行列による実分解。
方針：三つずつの因子を計算し、逆ブロックとの積の単位式を使う。
規約：KST Proposition 4.14、SW92 Proposition 1.5 の生成系を Whitehead 分解で置き換える。
使われ方：有限支持の外の逆ブロックを加え、整数行列の作用を単冪行列へ移す。 -/
lemma whiteheadBlockFactorization (g : (Matrix ι ι R)ˣ) :
    ((blockUpperUnit g.val * blockLowerUnit (-(g⁻¹).val) * blockUpperUnit g.val *
        blockUpperUnit (-1 : Matrix ι ι R) * blockLowerUnit (1 : Matrix ι ι R) *
        blockUpperUnit (-1 : Matrix ι ι R)) : (Matrix (ι ⊕ ι) (ι ⊕ ι) R)ˣ).val =
      Matrix.fromBlocks g.val 0 0 (g⁻¹).val := by
  have hgg : g.val * (g⁻¹).val = 1 := congrArg Units.val (mul_inv_cancel g)
  have hgg' : (g⁻¹).val * g.val = 1 := congrArg Units.val (inv_mul_cancel g)
  simp [blockUpperUnit, blockLowerUnit, Matrix.fromBlocks_multiply, hgg, hgg', mul_add, add_mul]

end SerrePositivity.KST.ProExcision
