module

public import SerrePositivity.AlgebraicGeometry.BorderedPivotDeterminant
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の単元ピボットと次次数の消滅からの関係式の因子分解。
方針：一行一列を追加した境界小行列式に Schur 補元の消滅を適用する。
規約：ピボットの可逆性と次次数の零イデアル条件を明示する。
使われ方：核全体をピボットの関係式で生成し、補成分と対象の実同型を得る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped Matrix

variable {R m n : Type*} [CommRing R] {k : ℕ}
  (H : Matrix m n R) (r : Fin k → m) (c : Fin k → n) [Invertible (H.submatrix r c)]

/--
概要：選んだピボットの逆行列で求める各関係式の係数行列。
方針：ピボット行の成分に逆行列を掛ける。
規約：KST §5、Stacks 0810, Lemma 38.30.2、行列の元の列数は有限とは限らない。
使われ方：全関係式を選んだピボット列から生成する実際の因子分解。
-/
def minorPivotColumnCoefficients : Matrix (Fin k) n R :=
  fun l j => (⅟(H.submatrix r c) *ᵥ (fun t => H (r t) j)) l

/--
概要：次次数の小行列式が全て零なら、元の行列は選んだピボット列と係数行列の積。
方針：各係数について境界行列式の消滅から Schur 補元の等式を得る。
規約：KST §5、Stacks 0810, Lemma 38.30.2、基礎環の整域性は不要。
使われ方：表示の核がピボット列から生成されることを証明する。
-/
theorem eq_selectedColumns_mul_of_succ_minorIdeal_eq_bot
    (hzero : matrixMinorIdeal H (k + 1) = ⊥) :
    H = (H.submatrix id c) * minorPivotColumnCoefficients H r c := by
  ext i j
  have hd := borderedPivotMatrix_mem_succ_minorIdeal H r c i j
  rw [hzero] at hd
  have hdet : (borderedPivotMatrix (H.submatrix r c) (fun l => H (r l) j)
      (fun l => H i (c l)) (H i j)).det = 0 := hd
  have h := borderedPivotMatrix_residual_eq_zero (H.submatrix r c)
    (fun l => H (r l) j) (fun l => H i (c l)) (H i j) hdet
  exact sub_eq_zero.mp h

include r in
/--
概要：可逆なピボットと次次数の消滅の下で、ピボット列は元の全ての列と同じ部分加群を生成する。
方針：実際の因子分解で一方向の包含を、選んだ列の所属で逆方向を示す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、元の列の有限性は不要。
使われ方：完全な関係式の核をピボットの自由な関係式に置き換える。
-/
theorem columnSpan_eq_selectedColumns_of_succ_minorIdeal_eq_bot
    (hzero : matrixMinorIdeal H (k + 1) = ⊥) :
    Submodule.span R (Set.range H.col) =
      Submodule.span R (Set.range (H.submatrix id c).col) := by
  apply le_antisymm
  · rw [← Matrix.range_mulVecLin (H.submatrix id c)]
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    refine ⟨(minorPivotColumnCoefficients H r c).col j, ?_⟩
    ext i
    exact (congrArg (fun A : Matrix m n R => A i j)
      (eq_selectedColumns_mul_of_succ_minorIdeal_eq_bot H r c hzero)).symm
  · apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    exact Submodule.subset_span ⟨c j, rfl⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
