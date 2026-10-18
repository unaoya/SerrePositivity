module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# 単位とのブロック和による行列の安定化

概要：行列へ単位の一成分を付け加える積と単位を保つ写像を構成する。
方針：直和添字でブロック和を取り、有限順序集合へ添字を付け替える。
規約：KST 式 (2.3)、Lemma 2.13 の安定 rank。加法を保つ写像とは主張しない。
使われ方：ĜL_r の順序列の遷移。
-/

@[expose] public section
namespace SerrePositivity.KST.Comparison

/--
概要：行列と一次元の単位のブロック和。
方針：二つの非対角ブロックを零にする。
規約：添字は Fin r と Fin 1 の直和。
使われ方：有限 rank の行列の安定化の積保存。
-/
def matrixBlockUnit (R : Type*) [Semiring R] (r : ℕ) :
    Matrix (Fin r) (Fin r) R →* Matrix (Fin r ⊕ Fin 1) (Fin r ⊕ Fin 1) R where
  toFun a := Matrix.fromBlocks a 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' a b := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]

/--
概要：行列の rank を一つ増やす安定化写像。
方針：単位とのブロック和の添字を Fin (r + 1) へ付け替える。
規約：積と単位を保つモノイド準同型。
使われ方：単体的環の ĜL の安定化。
-/
def matrixStabilization (R : Type*) [Semiring R] (r : ℕ) :
    Matrix (Fin r) (Fin r) R →* Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  (Matrix.reindexRingEquiv R (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r + 1))).toMonoidHom.comp
    (matrixBlockUnit R r)

/--
概要：単位とのブロック和は係数環の準同型と可換。
方針：零と単位の保存を各ブロックで計算する。
規約：係数環は非可換でもよい。
使われ方：面・退化と安定化の自然性。
-/
theorem matrixBlockUnit_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (r : ℕ) (a : Matrix (Fin r) (Fin r) R) :
    f.mapMatrix (matrixBlockUnit R r a) = matrixBlockUnit S r (f.mapMatrix a) := by
  ext i j
  rcases i with (i | i) <;> rcases j with (j | j)
  · rfl
  · exact f.map_zero
  · exact f.map_zero
  · change f ((1 : Matrix (Fin 1) (Fin 1) R) i j) =
      (1 : Matrix (Fin 1) (Fin 1) S) i j
    simp only [Matrix.one_apply, apply_ite f, f.map_one, f.map_zero]

/--
概要：有限 rank の行列の安定化は係数環の準同型と可換。
方針：ブロック和と添字の付け替えの計算を使う。
規約：全ての成分で厳密な等式となる。
使われ方：単体的モノイドの安定化の自然変換。
-/
theorem matrixStabilization_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (r : ℕ) (a : Matrix (Fin r) (Fin r) R) :
    f.mapMatrix (matrixStabilization R r a) = matrixStabilization S r (f.mapMatrix a) := by
  have h := matrixBlockUnit_map f r a
  ext i j
  exact congrArg (fun m => m (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) h

end SerrePositivity.KST.Comparison
