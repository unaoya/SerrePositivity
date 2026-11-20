module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ModuleMittagLeffler
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
概要：KST §5、Stacks 05A9・05FS の平坦加群の Mittag–Leffler 性の忠実平坦降下。
方針：試験族の各基底変更写像の積に平坦加群をテンソルし、基底変更の取消で比較する。
規約：元の加群の平坦性を明示する。加群の有限性は降下自体には不要。
使われ方：Noether 基底上の可算生成平坦加群の射影性の忠実平坦降下。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：基底変更した左因子と既に拡張環上の右因子のテンソルを、元の環上のテンソルへ戻す。
方針：テンソルの交換、基底変更の取消、再度の交換を合成する。
規約：KST §5、Stacks 05A9・05FS、同型は元の環上で保持する。
使われ方：試験族を基底変更した後の積比較を元の平坦加群のテンソルへ戻す。
-/
def baseChangedLeftTensorEquiv
    (R T M D : Type u) [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [Module R M] [AddCommGroup D] [Module R D] [Module T D]
    [IsScalarTower R T D] :
    ((T ⊗[R] M) ⊗[T] D) ≃ₗ[R] M ⊗[R] D :=
  (TensorProduct.comm T (T ⊗[R] M) D).restrictScalars R ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R T T D M).restrictScalars R ≪≫ₗ
      TensorProduct.comm R D M

/--
概要：基底変更した左因子の取消の逆は、左の元に一をテンソルする。
方針：二つの交換と基底変更取消の純テンソル公式を使う。
規約：KST §5、Stacks 05A9・05FS、右因子は既に拡張環上の加群。
使われ方：積比較の基底変更の成分式。
-/
theorem baseChangedLeftTensorEquiv_symm_tmul
    (R T M D : Type u) [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [Module R M] [AddCommGroup D] [Module R D] [Module T D]
    [IsScalarTower R T D] (m : M) (d : D) :
    (baseChangedLeftTensorEquiv R T M D).symm (m ⊗ₜ[R] d) =
      ((1 : T) ⊗ₜ[R] m) ⊗ₜ[T] d := by
  simp [baseChangedLeftTensorEquiv]

/--
概要：平坦加群の Mittag–Leffler 性は忠実平坦な基底変更から降下する。
方針：各試験加群の基底変更の積を平坦な元の加群とテンソルし、その単射を拡張環上の比較へ送る。
規約：KST §5、Stacks 05A9・05FS、元の加群は平坦。Noether 性も可算生成性も不要。
使われ方：有限型代数の射影性の存在の忠実平坦被覆。
-/
theorem isModuleMittagLeffler_of_faithfullyFlat
    (R T M : Type u) [CommRing R] [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hM : IsModuleMittagLeffler T (T ⊗[R] M)) : IsModuleMittagLeffler R M := by
  intro ι N hN hRN
  let D := ∀ i, T ⊗[R] N i
  let j : (∀ i, N i) →ₗ[R] D :=
    LinearMap.pi (fun i => (TensorProduct.mk R T (N i) 1).comp (LinearMap.proj i))
  have hj : Function.Injective j := by
    intro x y hxy
    funext i
    exact (Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := T) (N i))
      (congrFun hxy i)
  let E := baseChangedLeftTensorEquiv R T M D
  let g := E.symm.toLinearMap.comp (j.lTensor M)
  have hg : Function.Injective g :=
    E.symm.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap j hj)
  have hcomponent (x : M ⊗[R] (∀ i, N i)) (i : ι) :
      TensorProduct.piRightHom T T (T ⊗[R] M) (fun i => T ⊗[R] N i) (g x) i =
      TensorProduct.AlgebraTensorModule.distribBaseChange R T M (N i)
        ((1 : T) ⊗ₜ[R] (TensorProduct.piRightHom R R M N x i)) := by
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
        change TensorProduct.piRightHom T T (T ⊗[R] M) (fun i => T ⊗[R] N i)
          (E.symm (m ⊗ₜ[R] j n)) i = _
        rw [baseChangedLeftTensorEquiv_symm_tmul]
        rfl
    | add x y hx hy =>
        simp only [map_add, Pi.add_apply, TensorProduct.tmul_add, hx, hy]
  intro x y hxy
  apply hg
  apply hM ι (fun i => T ⊗[R] N i)
  funext i
  rw [hcomponent, hcomponent, hxy]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
