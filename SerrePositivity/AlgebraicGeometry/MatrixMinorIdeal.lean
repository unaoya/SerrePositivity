module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の表示行列の小行列式イデアル。
方針：行と列の選択による正方小行列の行列式でイデアルを生成する。
規約：重複した行・列の選択も許し、表示から独立な Fitting イデアルとはまだ同定しない。
使われ方：平坦化中心の係数を取る前の表示行列の計算。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R S : Type*} [CommRing R] [CommRing S] {m n : Type*}

/--
概要：行列の k 次小行列式が生成するイデアル。
方針：Fin(k) からの行選択と列選択を全て走らせる。
規約：KST §5、Stacks 0810, Lemma 38.30.2、零次と空行列も含む。
使われ方：選んだ有限表示行列についての Fitting の計算の基礎。
-/
def matrixMinorIdeal (A : Matrix m n R) (k : ℕ) : Ideal R :=
  Ideal.span (Set.range fun p : (Fin k → m) × (Fin k → n) =>
    (A.submatrix p.1 p.2).det)

/--
概要：指定した小行列式は小行列式イデアルに属する。
方針：生成集合の元であることを使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、選択写像の単射性は不要。
使われ方：行列式の展開と基底変更の所属計算。
-/
theorem det_submatrix_mem_matrixMinorIdeal (A : Matrix m n R) (k : ℕ)
    (r : Fin k → m) (c : Fin k → n) : (A.submatrix r c).det ∈ matrixMinorIdeal A k :=
  Ideal.subset_span ⟨(r, c), rfl⟩

/--
概要：有限行列の小行列式イデアルは有限生成。
方針：固定次数の行と列の選択の集合が有限であることを使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、環の Noether 性は不要。
使われ方：係数中心の元となる有限生成イデアル。
-/
theorem matrixMinorIdeal_fg [Finite m] [Finite n] (A : Matrix m n R) (k : ℕ) :
    (matrixMinorIdeal A k).FG :=
  Submodule.fg_span (Set.finite_range _)

/--
概要：零次小行列式イデアルは単位イデアル。
方針：空行列の行列式が一であることを使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、元の行列の行や列が空でも成立。
使われ方：表示の生成元数以上の Fitting 添字の規約。
-/
theorem matrixMinorIdeal_zero (A : Matrix m n R) : matrixMinorIdeal A 0 = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  simpa using det_submatrix_mem_matrixMinorIdeal A 0 Fin.elim0 Fin.elim0

/--
概要：小行列式イデアルは任意の環準同型による係数変更と可換。
方針：行列式と環準同型の可換性を生成集合の各元に適用する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、平坦な基底変更に限定しない。
使われ方：blowup チャート上で元の表示行列のイデアルを照合する。
-/
theorem matrixMinorIdeal_map (A : Matrix m n R) (k : ℕ) (φ : R →+* S) :
    (matrixMinorIdeal A k).map φ = matrixMinorIdeal (A.map φ) k := by
  rw [matrixMinorIdeal, Ideal.map_span]
  congr 1
  ext s
  constructor
  · rintro ⟨r, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, (φ.map_det (A.submatrix p.1 p.2)).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨(A.submatrix p.1 p.2).det, ⟨p, rfl⟩, φ.map_det _⟩

/--
概要：小行列式の次数を一つ増すとイデアルは小さくなる。
方針：最初の行に沿う Laplace 展開で一つ小さい小行列式の線形結合にする。
規約：KST §5、Stacks 0810, Lemma 38.30.2、元の行列は無限行列でもよい。
使われ方：隣接する Fitting 条件の比較。
-/
theorem matrixMinorIdeal_succ_le (A : Matrix m n R) (k : ℕ) :
    matrixMinorIdeal A (k + 1) ≤ matrixMinorIdeal A k := by
  apply Ideal.span_le.mpr
  rintro x ⟨⟨r, c⟩, rfl⟩
  change (A.submatrix r c).det ∈ matrixMinorIdeal A k
  rw [Matrix.det_succ_row_zero]
  apply (matrixMinorIdeal A k).sum_mem
  intro j _
  apply Ideal.mul_mem_left
  exact det_submatrix_mem_matrixMinorIdeal A k (r ∘ Fin.succ) (c ∘ j.succAbove)

/--
概要：次数が行数を越える小行列式イデアルは零。
方針：行選択に必ず重複があり、対応する小行列の行列式が零になる。
規約：KST §5、Stacks 0810, Lemma 38.30.2、列数には有限性を仮定しない。
使われ方：表示の行数で決まる小行列式の消滅範囲。
-/
theorem matrixMinorIdeal_eq_bot_of_rows_lt [Fintype m] (A : Matrix m n R)
    (k : ℕ) (hk : Fintype.card m < k) : matrixMinorIdeal A k = ⊥ := by
  apply le_antisymm _ bot_le
  apply Ideal.span_le.mpr
  rintro x ⟨⟨r, c⟩, rfl⟩
  change (A.submatrix r c).det = 0
  have hr : ¬ Function.Injective r := by
    intro hr
    have h := Fintype.card_le_of_injective r hr
    simp only [Fintype.card_fin] at h
    exact (Nat.not_le_of_gt hk) h
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hr
  apply Matrix.det_zero_of_row_eq hne
  ext l
  exact congrArg (fun t => A t (c l)) hij

/--
概要：行列の転置は同じ次数の小行列式イデアルを保つ。
方針：行選択と列選択を交換し、行列式の転置不変性を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、行・列の型は異なってよい。
使われ方：列数による小行列式の消滅を行数の場合から得る。
-/
theorem matrixMinorIdeal_transpose_le (A : Matrix m n R) (k : ℕ) :
    matrixMinorIdeal A.transpose k ≤ matrixMinorIdeal A k := by
  apply Ideal.span_le.mpr
  rintro x ⟨⟨r, c⟩, rfl⟩
  change ((A.submatrix c r).transpose).det ∈ matrixMinorIdeal A k
  rw [Matrix.det_transpose]
  exact det_submatrix_mem_matrixMinorIdeal A k c r

/--
概要：転置前後の小行列式イデアルは等しい。
方針：転置による包含を双方向に使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2。
使われ方：行・列に対称な消滅条件の照合。
-/
theorem matrixMinorIdeal_transpose (A : Matrix m n R) (k : ℕ) :
    matrixMinorIdeal A.transpose k = matrixMinorIdeal A k :=
  le_antisymm (matrixMinorIdeal_transpose_le A k) (matrixMinorIdeal_transpose_le A.transpose k)

/--
概要：次数が列数を越える小行列式イデアルは零。
方針：転置により行数の場合へ還元する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、行数には有限性を仮定しない。
使われ方：関係式の個数による小行列式の消滅範囲。
-/
theorem matrixMinorIdeal_eq_bot_of_cols_lt [Fintype n] (A : Matrix m n R)
    (k : ℕ) (hk : Fintype.card n < k) : matrixMinorIdeal A k = ⊥ := by
  rw [← matrixMinorIdeal_transpose]
  exact matrixMinorIdeal_eq_bot_of_rows_lt A.transpose k hk

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
