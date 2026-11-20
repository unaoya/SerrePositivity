module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.MatrixMinorIdealOperations
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の関係式の生成族によらない小行列式イデアル。
方針：列の生成する部分加群の包含から係数行列を実際に選んで積として表す。
規約：自由な標的加群は固定し、関係式の生成元数は変えてよい。
使われ方：固定した生成元に対する有限表示の関係式の選択を除く。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] {l m n : Type*}

/--
概要：列の生成する部分加群の包含から小行列式イデアルの包含が従う。
方針：各列を有限個の列の線形結合に表し、係数行列による右乗法を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、右側の列の添字集合だけに有限性を仮定。
使われ方：関係式の生成族を変えたときの比較。
-/
theorem matrixMinorIdeal_le_of_columnSpan_le [Finite l]
    (A : Matrix m n R) (B : Matrix m l R)
    (hspan : Submodule.span R (Set.range A.col) ≤ Submodule.span R (Set.range B.col))
    (k : ℕ) : matrixMinorIdeal A k ≤ matrixMinorIdeal B k := by
  classical
  let : Fintype l := Fintype.ofFinite l
  have hcol : ∀ j : n, ∃ c : l → R, ∑ t, c t • B.col t = A.col j := by
    intro j
    apply (Submodule.mem_span_range_iff_exists_fun R).mp
    exact hspan (Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using hcol
  let P : Matrix l n R := fun t j => c j t
  have hA : A = B * P := by
    ext i j
    change A i j = ∑ t, B i t * c j t
    calc
      A i j = (∑ t, c j t • B.col t) i := congrFun (hc j).symm i
      _ = ∑ t, B i t * c j t := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
        apply Finset.sum_congr rfl
        intro t _
        exact mul_comm _ _
  rw [hA]
  exact matrixMinorIdeal_mul_right_le B P k

/--
概要：列が同じ部分加群を生成すれば、小行列式イデアルは一致する。
方針：部分加群の等式から包含を双方向に適用する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、関係式の生成元数は同じでなくてよい。
使われ方：固定した自由加群への関係式の有限生成表示の選択からの独立性。
-/
theorem matrixMinorIdeal_eq_of_columnSpan_eq [Finite n] [Finite l]
    (A : Matrix m n R) (B : Matrix m l R)
    (hspan : Submodule.span R (Set.range A.col) = Submodule.span R (Set.range B.col))
    (k : ℕ) : matrixMinorIdeal A k = matrixMinorIdeal B k :=
  le_antisymm (matrixMinorIdeal_le_of_columnSpan_le A B hspan.le k)
    (matrixMinorIdeal_le_of_columnSpan_le B A hspan.ge k)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
