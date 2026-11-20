module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PureTransformCongr
public import SerrePositivity.AlgebraicGeometry.FlatPureTransformBaseChange
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
概要：KST §5、Stacks 0815 の二段の基底変更を経た純変換と元の加群の純変換の比較。
方針：テンソル積の係数の打ち消し同型と境界の像の等式を商へ移す。
規約：R、最初の係数環 A、追加の係数環 B を区別する。
使われ方：局所平坦化中心の追加 blowup と共通細分による平坦性の保存。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable (R A B M : Type*) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [AddCommGroup M] [Module R M] (f : R)

/--
概要：二段の基底変更による純変換と直接の基底変更による純変換の線形同型。
方針：テンソル積の係数の打ち消しと境界元の係数写像の一致を使う。
規約：KST §5、Stacks 0815、境界元は元の環 R で指定する。
使われ方：チャートをさらに blowup したときの純変換の照合。
-/
def tensorPureTransformCancelBaseChange :
    modulePureTransform (algebraMap A B (algebraMap R A f)) (B ⊗[A] (A ⊗[R] M)) ≃ₗ[B]
      modulePureTransform (algebraMap R B f) (B ⊗[R] M) :=
  (modulePureTransformCongr (algebraMap A B (algebraMap R A f))
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M)).trans
    (modulePureTransformBoundaryCongr _ (IsScalarTower.algebraMap_apply R A B f).symm)

/--
概要：二段の基底変更で得られた純変換の平坦性を直接の基底変更へ移す。
方針：実際の純変換の打ち消し同型を逆向きに使う。
規約：KST §5、Stacks 0815、平坦性は最終係数環 B についてのもの。
使われ方：局所平坦化の結論を元の加群について表す。
-/
theorem tensorPureTransform_flat_cancelBaseChange
    [Module.Flat B (modulePureTransform (algebraMap A B (algebraMap R A f))
      (B ⊗[A] (A ⊗[R] M)))] :
    Module.Flat B (modulePureTransform (algebraMap R B f) (B ⊗[R] M)) :=
  Module.Flat.of_linearEquiv (tensorPureTransformCancelBaseChange R A B M f).symm

/--
概要：平坦化した基底変更加群の純変換は、正則な境界を保つ任意の追加係数拡大でも平坦。
方針：Noether 環上の純変換の安定性と二段のテンソル積の打ち消しを使う。
規約：KST §5、Stacks 0815、Noether 条件は中間係数環 A に課す。
使われ方：局所中心をまとめる共通細分後の平坦性の保存。
-/
theorem tensorPureTransform_flat_baseChange [IsNoetherianRing A] [Module.Finite R M]
    [Module.Flat A (modulePureTransform (algebraMap R A f) (A ⊗[R] M))]
    (hf : IsRegular (algebraMap R B f)) :
    Module.Flat B (modulePureTransform (algebraMap R B f) (B ⊗[R] M)) := by
  have hf' : IsRegular (algebraMap A B (algebraMap R A f)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact hf
  have := flatPureTransform_baseChange B (algebraMap R A f) (A ⊗[R] M) hf'
  exact tensorPureTransform_flat_cancelBaseChange R A B M f

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
