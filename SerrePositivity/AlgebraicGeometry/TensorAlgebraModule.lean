module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
概要：KST §5、Stacks 0815, Theorem 38.30.7 の基底変更加群への基底変更代数の作用。
方針：右因子の作用を基底変更した線形自己準同型で表し、可換する左作用と合わせる。
規約：二つの環の作用の混同を避けるため大域インスタンスにはしない。
使われ方：有限型代数上有限な加群のチャートへの基底変更の有限性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable (R B C M : Type*) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [AddCommGroup M] [Module R M] [Module B M]
  [IsScalarTower R B M]

/--
概要：元の代数の作用を基底変更加群の線形自己準同型として表す。
方針：元の作用の代数準同型と自己準同型の基底変更を合成する。
規約：KST §5、Stacks 0815, Theorem 38.30.7、自己準同型は C 上線形。
使われ方：テンソル積の右因子からの B の作用。
-/
def tensorRightRepresentation : B →ₐ[R] Module.End C (C ⊗[R] M) :=
  (Module.End.baseChangeHom R C M).comp (Algebra.lsmul R R M)

/--
概要：基底変更加群への元の代数の右因子からの加群構造。
方針：線形自己準同型の環を介してスカラーを制限する。
規約：KST §5、Stacks 0815, Theorem 38.30.7、明示的に選ぶデータであり大域インスタンスではない。
使われ方：基底変更代数の加群構造の構成。
-/
@[instance_reducible]
def tensorRightModule : Module B (C ⊗[R] M) :=
  Module.compHom (C ⊗[R] M) (tensorRightRepresentation R B C M).toRingHom

/--
概要：右因子の作用は純テンソルの加群の因子だけに作用する。
方針：作用の基底変更の純テンソル上の定義を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、選んだ右因子加群構造についての式。
使われ方：基底変更代数上の有限生成性の証明。
-/
theorem tensorRightModule_smul_tmul (b : B) (c : C) (m : M) :
    letI : Module B (C ⊗[R] M) := tensorRightModule R B C M
    b • (c ⊗ₜ[R] m) = c ⊗ₜ[R] (b • m) := rfl

/--
概要：右因子からの作用は元の基礎環の作用と両立する。
方針：作用の代数準同型が基礎環の係数を保つことを使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、基礎環 R の像の作用を比較する。
使われ方：右因子の加群構造のスカラー塔。
-/
theorem tensorRightModule_algebraMap_smul (r : R) (z : C ⊗[R] M) :
    letI : Module B (C ⊗[R] M) := tensorRightModule R B C M
    algebraMap R B r • z = r • z := by
  change tensorRightRepresentation R B C M (algebraMap R B r) z = r • z
  have h := congrArg (fun k : Module.End C (C ⊗[R] M) => k z)
    ((tensorRightRepresentation R B C M).commutes r)
  simpa only [Module.algebraMap_end_apply] using h

/--
概要：右因子の加群構造は基礎環とのスカラー塔を持つ。
方針：基礎環の像の作用の一致を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、右因子の加群構造に対する定理。
使われ方：二つの代数のテンソル積からの作用の構成。
-/
theorem tensorRightModule_isScalarTower :
    letI : Module B (C ⊗[R] M) := tensorRightModule R B C M
    IsScalarTower R B (C ⊗[R] M) := by
  let : Module B (C ⊗[R] M) := tensorRightModule R B C M
  exact IsScalarTower.of_algebraMap_smul (tensorRightModule_algebraMap_smul R B C M)

/--
概要：右因子の作用と C の左作用は可換。
方針：右作用を表す自己準同型の C 線形性を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、作用の順序を明示する。
使われ方：基底変更代数上の加群構造。
-/
theorem tensorRightModule_smulCommClass :
    letI : Module B (C ⊗[R] M) := tensorRightModule R B C M
    SMulCommClass C B (C ⊗[R] M) := by
  let : Module B (C ⊗[R] M) := tensorRightModule R B C M
  exact ⟨fun c b z => ((tensorRightRepresentation R B C M b).map_smul c z).symm⟩

/--
概要：基底変更加群を基底変更代数の加群とする明示的な構造。
方針：可換する二つの代数の作用から Mathlib のテンソル積の加群構造を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、大域インスタンスに登録しない。
使われ方：基底変更後の有限性と Noether 性の照合。
-/
@[instance_reducible]
def tensorAlgebraModule : Module (C ⊗[R] B) (C ⊗[R] M) := by
  letI : Module B (C ⊗[R] M) := tensorRightModule R B C M
  letI : IsScalarTower R B (C ⊗[R] M) := tensorRightModule_isScalarTower R B C M
  letI : SMulCommClass C B (C ⊗[R] M) := tensorRightModule_smulCommClass R B C M
  exact TensorProduct.Algebra.module

/--
概要：基底変更代数の純テンソルの作用の公式。
方針：テンソル積の作用を構成する持ち上げの定義を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、作用は選んだ明示的構造。
使われ方：有限生成元の像による生成の証明。
-/
theorem tensorAlgebraModule_tmul_smul (c : C) (b : B) (z : C ⊗[R] M) :
    letI : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
    (c ⊗ₜ[R] b) • z = c • tensorRightRepresentation R B C M b z := rfl

/--
概要：基底変更代数の作用を二つの純テンソル上で計算する。
方針：右作用の基底変更の公式と C の左作用を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、係数の積の順序を固定する。
使われ方：基底変更代数上の生成性の計算。
-/
theorem tensorAlgebraModule_tmul_smul_tmul (c c' : C) (b : B) (m : M) :
    letI : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
    (c ⊗ₜ[R] b) • (c' ⊗ₜ[R] m) = (c * c') ⊗ₜ[R] (b • m) := rfl

/--
概要：基底変更代数からの作用は C の係数作用と両立する。
方針：C の像を c ⊗ 1 と表して作用の公式を使う。
規約：KST §5、Stacks 0815, Theorem 38.30.7、標準の左代数構造を使う。
使われ方：基底変更代数の Noether 性から境界ねじれの一様性を導く。
-/
theorem tensorAlgebraModule_isScalarTower_left :
    letI : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
    IsScalarTower C (C ⊗[R] B) (C ⊗[R] M) := by
  let : Module (C ⊗[R] B) (C ⊗[R] M) := tensorAlgebraModule R B C M
  apply IsScalarTower.of_algebraMap_smul
  intro c z
  change (c ⊗ₜ[R] (1 : B)) • z = c • z
  rw [tensorAlgebraModule_tmul_smul, map_one]
  rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
