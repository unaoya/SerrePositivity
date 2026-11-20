module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientIdeal
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の分裂した代数の係数表示の基底変更。
方針：直和のテンソル同型と二つの分裂写像のテンソル基底変更を合成する。
規約：分裂を明示的に構成し、係数環の平坦性は仮定しない。
使われ方：係数イデアルの blowup チャート上の拡大を計算する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R B C ι : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/--
概要：代数の直和への埋め込みを係数環のテンソル基底変更先で表す。
方針：埋め込みの基底変更と直和のテンソル同型を合成する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、添字集合は任意。
使われ方：基底変更代数の係数イデアルの定義。
-/
def splitAlgebraTensorEmbedding (e : B →ₗ[R] (ι →₀ R)) :
    (C ⊗[R] B) →ₗ[C] (ι →₀ C) := by
  classical
  exact (TensorProduct.finsuppScalarRight R C C ι).toLinearMap.comp (e.baseChange C)

/--
概要：代数への直和からの射影を係数環のテンソル基底変更先で表す。
方針：直和のテンソル同型の逆と射影の基底変更を合成する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、分裂の恒等式は別に証明する。
使われ方：基底変更先の係数表示が再び分裂することを確認する。
-/
def splitAlgebraTensorRetraction (p : (ι →₀ R) →ₗ[R] B) :
    (ι →₀ C) →ₗ[C] (C ⊗[R] B) := by
  classical
  exact (p.baseChange C).comp (TensorProduct.finsuppScalarRight R C C ι).symm.toLinearMap

/--
概要：係数埋め込みの純テンソルの各係数は、元の係数の像の係数環の元による倍。
方針：直和のテンソル同型と基底変更写像の公式を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、係数の乗法順を固定する。
使われ方：元の係数イデアルの像との比較。
-/
theorem splitAlgebraTensorEmbedding_tmul (e : B →ₗ[R] (ι →₀ R)) (c : C) (b : B) (i : ι) :
    splitAlgebraTensorEmbedding e (c ⊗ₜ[R] b) i = algebraMap R C (e b i) * c := by
  classical
  simp [splitAlgebraTensorEmbedding, TensorProduct.finsuppScalarRight_apply_tmul_apply,
    Algebra.smul_def]

/--
概要：直和への分裂は任意のテンソル基底変更で再び分裂する。
方針：基底変更の合成則と元の分裂等式を使い、直和同型とその逆を消去する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、係数環の平坦性は不要。
使われ方：基底変更先にも係数イデアルの生成元への還元を適用する。
-/
theorem splitAlgebraTensorRetraction_comp_embedding (e : B →ₗ[R] (ι →₀ R))
    (p : (ι →₀ R) →ₗ[R] B) (hpe : p.comp e = LinearMap.id) :
    (splitAlgebraTensorRetraction (C := C) p).comp (splitAlgebraTensorEmbedding e) =
      LinearMap.id := by
  classical
  have heq := congrArg (fun h : B →ₗ[R] B => h.baseChange C) hpe
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at heq
  apply LinearMap.ext
  intro x
  change p.baseChange C ((TensorProduct.finsuppScalarRight R C C ι).symm
    (TensorProduct.finsuppScalarRight R C C ι (e.baseChange C x))) = x
  rw [LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun heq x

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
