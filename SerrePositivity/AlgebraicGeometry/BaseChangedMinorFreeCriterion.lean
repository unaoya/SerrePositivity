module

public import SerrePositivity.AlgebraicGeometry.FiniteFreePresentationBaseChange
public import SerrePositivity.AlgebraicGeometry.LocalMinorFreeCriterion
public import SerrePositivity.AlgebraicGeometry.LocalPresentationMinorRank

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の基底変更した対象と元の小行列式イデアル。
方針：表示の任意の基底変更と小行列式イデアルの像の等式を局所環の自由性判定に接続する。
規約：係数環の平坦性は仮定しない。
使われ方：blowup チャートやその局所環で自由な純変換を作るための表示の計算。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R C M m n : Type*} [CommRing R] [CommRing C] [Algebra R C]
  [IsLocalRing C] [AddCommGroup M] [Module R M] [Fintype m] [Finite n]

/--
概要：小行列式イデアルの像が単位、次次数の像が零なら、基底変更した対象は所定階数の自由加群。
方針：係数変更行列の完全な表示を構成し、局所環上の小行列式の判定を適用する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、元の環の局所性は不要。
使われ方：基底上のイデアルの条件から、チャート上の実対象の自由性を導く。
-/
theorem tensor_free_and_finrank_of_minorIdeal_images
    (H : Matrix m n R) (k : ℕ) (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q)
    (hunit : (matrixMinorIdeal H k).map (algebraMap R C) = ⊤)
    (hzero : (matrixMinorIdeal H (k + 1)).map (algebraMap R C) = ⊥) :
    Module.Free C (C ⊗[R] M) ∧ Module.finrank C (C ⊗[R] M) = Fintype.card m - k := by
  classical
  exact free_and_finrank_of_unit_minorIdeal (H.map (algebraMap R C)) k
    (finiteFreePresentationBaseChange q) (finiteFreePresentationBaseChange_surjective q hq)
    (finiteFreePresentationBaseChange_columnSpan_eq_ker H q hq hH)
    ((matrixMinorIdeal_map H k (algebraMap R C)).symm.trans hunit)
    ((matrixMinorIdeal_map H (k + 1) (algebraMap R C)).symm.trans hzero)

/--
概要：基底変更した対象が局所環上射影的なら、元の小行列式イデアルの像の単位次数と消滅次数を特定できる。
方針：完全な基底変更表示に階数による小行列式条件を適用し、イデアルの像に戻す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、射影性は実際の基底変更対象についての条件。
使われ方：境界外の自由階数から、元のイデアルの局所化の単位と消滅を得る。
-/
theorem minorIdeal_images_at_tensor_finrank [Module.Projective C (C ⊗[R] M)]
    (H : Matrix m n R) (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q) :
    (matrixMinorIdeal H (Fintype.card m - Module.finrank C (C ⊗[R] M))).map
        (algebraMap R C) = ⊤ ∧
      ∀ j, Fintype.card m - Module.finrank C (C ⊗[R] M) < j →
        (matrixMinorIdeal H j).map (algebraMap R C) = ⊥ := by
  classical
  have h := minor_pattern_at_finrank_of_projective_presentation
    (finiteFreePresentationBaseChange (C := C) q)
    (finiteFreePresentationBaseChange_surjective q hq) (H.map (algebraMap R C))
    (finiteFreePresentationBaseChange_columnSpan_eq_ker H q hq hH)
  simpa only [matrixMinorIdeal_map] using h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
