module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.MatrixMinorIdeal

/-!
概要：KST §5、Stacks 080Z, Lemma 15.8.9 の小行列への制限と小行列式イデアル。
方針：制限後の行・列選択を元の選択写像と合成する。
規約：行列全体の行数・列数の有限性は不要。
使われ方：ピボットの列を選んだ関係式行列の小行列式を元のイデアルに戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：小行列への制限で小行列式イデアルは大きくならない。
方針：小行列の小行列を元の行列の小行列として表す。
規約：KST §5、Stacks 080Z, Lemma 15.8.9、選択写像の単射性は不要。
使われ方：選んだ関係式の有限部分の小行列式の所属。
-/
theorem matrixMinorIdeal_submatrix_le {R m n m' n' : Type*} [CommRing R]
    (A : Matrix m n R) (r : m' → m) (c : n' → n) (k : ℕ) :
    matrixMinorIdeal (A.submatrix r c) k ≤ matrixMinorIdeal A k := by
  apply Ideal.span_le.mpr
  rintro x ⟨p, rfl⟩
  exact det_submatrix_mem_matrixMinorIdeal A k (r ∘ p.1) (c ∘ p.2)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
