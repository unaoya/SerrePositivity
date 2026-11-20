module

public import SerrePositivity.AlgebraicGeometry.MatrixMinorIdealColumnSpan

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の分裂した自由関係式の小行列式。
方針：左逆元のある行列と単位行列の小行列式を比較し、列数による消滅を使う。
規約：分裂は実際の行列の等式として入力する。
使われ方：自由な対象の表示における小行列式の単位条件と消滅条件を導く。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R m n : Type*} [CommRing R]

/--
概要：小行列式イデアルは次数に関して反単調。
方針：一段の次数増加の包含を自然数の反単調性判定に適用する。
規約：KST §5、Stacks 0810, Lemma 38.30.2。
使われ方：生成元の階数の両側の小行列式条件を比較する。
-/
theorem matrixMinorIdeal_antitone (A : Matrix m n R) : Antitone (matrixMinorIdeal A) :=
  antitone_nat_of_succ_le (matrixMinorIdeal_succ_le A)

/--
概要：単位行列の最大次数の小行列式イデアルは単位イデアル。
方針：全ての行・列を選ぶ小行列式が一になることを使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、階数零も含む。
使われ方：左逆元を持つ関係式行列の小行列式の単位条件。
-/
theorem matrixMinorIdeal_one_top (k : ℕ) :
    matrixMinorIdeal (1 : Matrix (Fin k) (Fin k) R) k = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  simpa only [Matrix.submatrix_id_id, Matrix.det_one] using
    det_submatrix_mem_matrixMinorIdeal (1 : Matrix (Fin k) (Fin k) R) k id id

/--
概要：左逆元を持つ k 列の行列の k 次小行列式イデアルは単位イデアル。
方針：左逆元との積が単位行列であることと左乗法での包含を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、行の添字集合は有限。
使われ方：自由な直和因子となる関係式の単位条件。
-/
theorem matrixMinorIdeal_eq_top_of_leftInverse [Fintype m] {k : ℕ}
    (T : Matrix m (Fin k) R) (S : Matrix (Fin k) m R) (hST : S * T = 1) :
    matrixMinorIdeal T k = ⊤ := by
  apply top_unique
  have h := matrixMinorIdeal_mul_left_le S T k
  simpa only [hST, matrixMinorIdeal_one_top] using h

/--
概要：分裂した k 個の自由な関係式を生成する任意の有限行列の k 次は単位、k を越える次数は零。
方針：同じ列部分加群での不変性、左逆元、列数による消滅を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、元の関係式の生成元数は k と異なってよい。
使われ方：自由な対象の表示で、選んだ関係式行列に依存しない小行列式条件を得る。
-/
theorem matrixMinorIdeal_of_split_columnSpan [Fintype m] [Finite n] {k : ℕ}
    (H : Matrix m n R) (T : Matrix m (Fin k) R) (S : Matrix (Fin k) m R)
    (hST : S * T = 1)
    (hspan : Submodule.span R (Set.range H.col) = Submodule.span R (Set.range T.col)) :
    matrixMinorIdeal H k = ⊤ ∧ ∀ j, k < j → matrixMinorIdeal H j = ⊥ := by
  constructor
  · rw [matrixMinorIdeal_eq_of_columnSpan_eq H T hspan]
    exact matrixMinorIdeal_eq_top_of_leftInverse T S hST
  · intro j hj
    rw [matrixMinorIdeal_eq_of_columnSpan_eq H T hspan]
    exact matrixMinorIdeal_eq_bot_of_cols_lt T j (by simpa only [Fintype.card_fin] using hj)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
