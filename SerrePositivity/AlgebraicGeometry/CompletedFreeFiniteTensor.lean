module

public import SerrePositivity.AlgebraicGeometry.CompletedFreeEmbedding
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
概要：KST §5、Stacks 05BC の自由加群の完備化の積埋め込みと有限加群のテンソル積。
方針：既存の完備化・テンソル比較を有限台座標の完備化へ接続し、積埋め込みとの可換式を使う。
規約：CommutativeAlgebra の既証の比較を読み取り専用で利用し、その証明を複製しない。
使われ方：自由加群の完備化から積への埋め込みの普遍単射性。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：任意の加群と有限台自由加群のテンソル積を、その加群の有限台関数とする実際の線形同型。
方針：右因子の標準基底による Mathlib の座標同型を使う。
規約：KST §5、Stacks 05BC、基底の有限性は不要。
使われ方：完備化・テンソル比較の標的を係数の有限台関数へ移す。
-/
def freeTensorFinsuppEquiv (R A N : Type u) [CommRing R] [AddCommGroup N] [Module R N] :
    N ⊗[R] (A →₀ R) ≃ₗ[R] (A →₀ N) := by
  classical
  exact TensorProduct.equivFinsuppOfBasisRight (Finsupp.basisSingleOne : Module.Basis A R (A →₀ R))

/--
概要：有限台自由加群とのテンソル座標の純テンソル公式。
方針：右因子の標準基底の座標を計算する。
規約：KST §5、Stacks 05BC、係数の順序は v(a) による作用。
使われ方：完備化した座標と元の係数写像の交換式。
-/
theorem freeTensorFinsuppEquiv_tmul_apply
    (R A N : Type u) [CommRing R] [AddCommGroup N] [Module R N]
    (n : N) (v : A →₀ R) (a : A) :
    freeTensorFinsuppEquiv R A N (n ⊗ₜ[R] v) a = v a • n := by
  classical
  simp [freeTensorFinsuppEquiv]

/--
概要：加群と自由加群の完備化のテンソル積から、各係数加群の完備化の積への比較写像。
方針：既存の完備化・テンソル比較、有限台表示の完備化同型、座標比較を合成する。
規約：KST §5、Stacks 05BC、定義には Noether 性・有限性を課さない。
使われ方：有限加群の場合の普遍単射性を座標から検出する。
-/
def completedFreeTensorCoordinates
    {R : Type u} [CommRing R] (I : Ideal R) (A N : Type u) [AddCommGroup N] [Module R N] :
    N ⊗[R] AdicCompletion I (A →₀ R) →ₗ[R] (A → AdicCompletion I N) :=
  ((completedFinsuppCoordinates I A N).comp
    ((AdicCompletion.congr I (freeTensorFinsuppEquiv R A N)).restrictScalars R).toLinearMap).comp
      (SerrePositivity.adicCompletionTensorComparison I N (A →₀ R))

/--
概要：Noether 基底で有限加群の自由完備化テンソル座標比較は単射。
方針：既存の有限加群・平坦加群の完備化比較の単射性と二つの座標同型を合成する。
規約：KST §5、Stacks 05BC、有限台自由加群の平坦性を使う。
使われ方：有限加群とのテンソルによる積埋め込みの単射性。
-/
theorem completedFreeTensorCoordinates_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (A N : Type u)
    [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Function.Injective (completedFreeTensorCoordinates I A N) :=
  (completedFinsuppCoordinates_injective I A N).comp
    ((AdicCompletion.congr I (freeTensorFinsuppEquiv R A N)).injective.comp
      (SerrePositivity.adicCompletionTensorComparison_injective I N (A →₀ R)))

/--
概要：自由完備化とのテンソル座標比較は、各完備化係数に指定元を掛けた完備化を返す。
方針：線形写像の完備化の合成公式と有限台テンソル座標の純テンソル公式を使う。
規約：KST §5、Stacks 05BC、加群の有限性は公式には不要。
使われ方：積埋め込みのテンソルとの因子化式。
-/
theorem completedFreeTensorCoordinates_tmul_apply
    {R : Type u} [CommRing R] (I : Ideal R) (A N : Type u) [AddCommGroup N] [Module R N]
    (n : N) (x : AdicCompletion I (A →₀ R)) (a : A) :
    completedFreeTensorCoordinates I A N (n ⊗ₜ[R] x) a =
      AdicCompletion.map I (LinearMap.toSpanSingleton R N n)
        (AdicCompletion.map I (Finsupp.lapply a : (A →₀ R) →ₗ[R] R) x) := by
  let T := freeTensorFinsuppEquiv R A N
  have hcoeff : ((Finsupp.lapply a : (A →₀ N) →ₗ[R] N).comp T.toLinearMap).comp
      (TensorProduct.mk R N (A →₀ R) n) =
      (LinearMap.toSpanSingleton R N n).comp (Finsupp.lapply a) := by
    apply LinearMap.ext
    intro v
    exact freeTensorFinsuppEquiv_tmul_apply R A N n v a
  change AdicCompletion.map I (Finsupp.lapply a : (A →₀ N) →ₗ[R] N)
      (AdicCompletion.map I T.toLinearMap
        (AdicCompletion.map I (TensorProduct.mk R N (A →₀ R) n) x)) = _
  rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply, hcoeff,
    ← AdicCompletion.map_comp_apply]

/--
概要：基礎環が完備なら、テンソル座標比較の各係数は積埋め込みの係数と指定元の積の標準完備化。
方針：基礎環の完備化同型の逆の公式と標準写像の自然性を使う。
規約：KST §5、Stacks 05BC、元の自由完備化の積埋め込みと両立する。
使われ方：有限テンソルの単射性を元の積埋め込みへ戻す。
-/
theorem completedFreeTensorCoordinates_tmul_apply_of_complete
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (A N : Type u) [AddCommGroup N] [Module R N]
    (n : N) (x : AdicCompletion I (A →₀ R)) (a : A) :
    completedFreeTensorCoordinates I A N (n ⊗ₜ[R] x) a =
      AdicCompletion.of I N (completedFreeEmbedding I A x a • n) := by
  rw [completedFreeTensorCoordinates_tmul_apply]
  have hR : AdicCompletion.map I (Finsupp.lapply a : (A →₀ R) →ₗ[R] R) x =
      AdicCompletion.of I R (completedFreeEmbedding I A x a) := by
    exact ((AdicCompletion.ofLinearEquiv I R).apply_symm_apply
      (AdicCompletion.map I (Finsupp.lapply a) x)).symm
  rw [hR, AdicCompletion.map_of]
  rfl

/--
概要：完備な基礎環では自由完備化のテンソル座標比較は、積埋め込みのテンソルを通じて因子化する。
方針：純テンソル上で前の座標公式と係数積比較の公式を照合する。
規約：KST §5、Stacks 05BC、等式は実際の線形写像の間で述べる。
使われ方：座標比較の単射性から積埋め込みの有限テンソルの単射性を得る。
-/
theorem completedFreeTensorCoordinates_factor
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (A N : Type u) [AddCommGroup N] [Module R N] :
    completedFreeTensorCoordinates I A N =
      ((LinearMap.compLeft (AdicCompletion.of I N) A).comp
        (TensorProduct.piScalarRightHom R R N A)).comp
          ((completedFreeEmbedding I A).lTensor N) := by
  apply TensorProduct.ext'
  intro n x
  funext a
  rw [completedFreeTensorCoordinates_tmul_apply_of_complete]
  simp

/--
概要：自由完備化の積埋め込みは、Noether 基底上の任意の有限加群との左テンソルで単射。
方針：有限加群との座標比較の単射性を、積埋め込みを通る因子化式から戻す。
規約：KST §5、Stacks 05BC、試験加群には平坦性を要求しない。
使われ方：任意の加群とのテンソルの単射性への有限部分による移行。
-/
theorem completedFreeEmbedding_lTensor_injective_of_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (A N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Function.Injective ((completedFreeEmbedding I A).lTensor N) := by
  have h := completedFreeTensorCoordinates_injective I A N
  rw [completedFreeTensorCoordinates_factor] at h
  intro x y hxy
  apply h
  exact congrArg ((LinearMap.compLeft (AdicCompletion.of I N) A).comp
    (TensorProduct.piScalarRightHom R R N A)) hxy

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
