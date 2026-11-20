module

public import SerrePositivity.AlgebraicGeometry.MatrixTensorBaseChange

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の選んだ有限自由表示の任意の基底変更。
方針：自由加群のテンソル同型で行列を照合し、テンソル積の右完全性を使う。
規約：係数環の平坦性は仮定しない。
使われ方：基底変更された表示行列に局所的な小行列式判定を適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R C M m : Type*} [CommRing R] [CommRing C] [Algebra R C]
  [AddCommGroup M] [Module R M] [Fintype m] [DecidableEq m]

/--
概要：有限自由な生成元の写像を基底変更し、係数環上の自由加群を始域とする。
方針：標準の自由加群のテンソル同型の逆と基底変更写像を合成する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、始域の基底は固定する。
使われ方：基底変更した有限表示の実際の生成全射。
-/
def finiteFreePresentationBaseChange (q : (m → R) →ₗ[R] M) :
    (m → C) →ₗ[C] (C ⊗[R] M) :=
  (q.baseChange C).comp (TensorProduct.piScalarRight R C C m).symm.toLinearMap

/--
概要：生成全射の基底変更は再び全射。
方針：テンソル基底変更の全射性と自由加群の標準同型を合成する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、平坦性は不要。
使われ方：基底変更先の有限生成元の指定。
-/
theorem finiteFreePresentationBaseChange_surjective (q : (m → R) →ₗ[R] M)
    (hq : Function.Surjective q) :
    Function.Surjective (finiteFreePresentationBaseChange (C := C) q) :=
  (q.baseChange_surjective C hq).comp (TensorProduct.piScalarRight R C C m).symm.surjective

/--
概要：完全な有限自由表示は、行列の係数変更と生成全射の基底変更によって完全なまま保たれる。
方針：テンソル積の右完全性を二つの自由加群の標準同型で移す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、元の列が核全体を生成することを仮定する。
使われ方：小行列式の基底変更の公式を実際の対象の表示に適用する。
-/
theorem finiteFreePresentationBaseChange_exact {n : Type*} [Fintype n]
    (H : Matrix m n R) (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q) :
    Function.Exact (H.map (algebraMap R C)).mulVecLin
      (finiteFreePresentationBaseChange (C := C) q) := by
  classical
  have hex : Function.Exact H.mulVecLin q := by
    apply LinearMap.exact_iff.mpr
    rw [Matrix.range_mulVecLin]
    exact hH.symm
  have hten : Function.Exact (H.mulVecLin.baseChange C) (q.baseChange C) := by
    simpa only [LinearMap.baseChange_eq_lTensor] using lTensor_exact C hex hq
  apply (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := TensorProduct.piScalarRight R C C n)
    (e₂ := TensorProduct.piScalarRight R C C m)
    (e₃ := LinearEquiv.refl C (C ⊗[R] M)) (matrixTensorBaseChange_square H).symm ?_).mpr hten
  apply LinearMap.ext
  intro z
  change q.baseChange C ((TensorProduct.piScalarRight R C C m).symm
    (TensorProduct.piScalarRight R C C m z)) = q.baseChange C z
  rw [LinearEquiv.symm_apply_apply]

/--
概要：係数変更した関係式行列の列は、新しい生成全射の核全体を生成する。
方針：基底変更した表示の完全性を核と列部分加群の等式に書き換える。
規約：KST §5、Stacks 0810, Lemma 38.30.2、基底変更は任意。
使われ方：局所環上の小行列式による自由性と階数の判定の入力。
-/
theorem finiteFreePresentationBaseChange_columnSpan_eq_ker {n : Type*} [Finite n]
    (H : Matrix m n R) (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q) :
    Submodule.span C (Set.range (H.map (algebraMap R C)).col) =
      LinearMap.ker (finiteFreePresentationBaseChange (C := C) q) := by
  let : Fintype n := Fintype.ofFinite n
  have h := (finiteFreePresentationBaseChange_exact (C := C) H q hq hH).linearMap_ker_eq
  rw [Matrix.range_mulVecLin] at h
  exact h.symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
