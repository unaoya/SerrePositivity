module

public import SerrePositivity.AlgebraicGeometry.LocalPresentationSplitMatrix
public import SerrePositivity.AlgebraicGeometry.PresentationKernelProduct

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の局所自由な対象の表示行列の小行列式の次数。
方針：実際の核の分裂行列の列数を、核と対象の階数の和から特定する。
規約：任意の完全な有限関係式行列を扱い、Fitting の表示独立性を仮定しない。
使われ方：境界外の自由階数から小行列式の単位条件と消滅条件を得る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped Matrix

/--
概要：局所環上の射影的な対象の有限自由表示では、関係式の階数は生成元数から対象の階数を引いた数。
方針：核の実際の分裂行列から核の階数を計算し、表示の直積分解の階数の等式を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、関係式の有限生成族が核全体を生成する。
使われ方：自由な対象における Fitting 型の単位次数と消滅の正確な添字。
-/
theorem minor_pattern_at_finrank_of_projective_presentation
    {R M m n : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] [Fintype m] [Finite n]
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q) (H : Matrix m n R)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q) :
    matrixMinorIdeal H (Fintype.card m - Module.finrank R M) = ⊤ ∧
      ∀ j, Fintype.card m - Module.finrank R M < j → matrixMinorIdeal H j = ⊥ := by
  classical
  obtain ⟨k, T, S, hST, hT⟩ := exists_split_matrix_for_local_presentation_kernel q hq
  have htinj : Function.Injective T.mulVecLin := by
    intro x y hxy
    have h := congrArg S.mulVecLin hxy
    change S *ᵥ (T *ᵥ x) = S *ᵥ (T *ᵥ y) at h
    simpa only [Matrix.mulVec_mulVec, hST, Matrix.one_mulVec] using h
  have hK : Module.finrank R (LinearMap.ker q) = k := by
    rw [← hT, ← Matrix.range_mulVecLin, LinearMap.finrank_range_of_inj htinj,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hcard : k + Module.finrank R M = Fintype.card m := by
    simpa only [hK, Module.finrank_fintype_fun_eq_card] using presentationKernel_finrank_add q hq
  have hk : k = Fintype.card m - Module.finrank R M := by omega
  simpa only [hk] using matrixMinorIdeal_of_split_columnSpan H T S hST (hH.trans hT.symm)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
