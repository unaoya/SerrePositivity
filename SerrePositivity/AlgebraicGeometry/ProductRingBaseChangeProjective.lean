module

public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarRestriction
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Algebra.Prod

/-!
概要：KST §5、Stacks 05FS の積環への基底変更の射影性。
方針：各因子を積環の直和因子とし、射影性のスカラー制限とテンソルの積分配を使う。
規約：積環の各因子への代数構造と加群構造は証明内で明示する。
使われ方：局所化と完備化の各々での射影性を一つの忠実平坦拡大上へまとめる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：二つの代数への基底変更が各々射影的なら、積環への基底変更も積環上射影的。
方針：因子の係数を積環へ線形に戻す分裂と、テンソルの積への分配同型を構成する。
規約：KST §5、Stacks 05FS、元の加群の平坦性はこの組み立てには不要。
使われ方：局所化と完備化の射影性から忠実平坦降下を適用する。
-/
theorem projective_baseChange_product_of_factors
    (R A B M : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M]
    [Module.Projective A (A ⊗[R] M)] [Module.Projective B (B ⊗[R] M)] :
    Module.Projective (A × B) ((A × B) ⊗[R] M) := by
  let : Algebra (A × B) A := (RingHom.fst A B).toAlgebra
  let : Algebra (A × B) B := (RingHom.snd A B).toAlgebra
  let iA : A →ₗ[A × B] A × B :=
    { toFun := fun a => (a, 0)
      map_add' := by intro x y; ext <;> simp
      map_smul' := by
        intro r a
        change (r.1 * a, 0) = (r.1 * a, r.2 * 0)
        simp }
  let iB : B →ₗ[A × B] A × B :=
    { toFun := fun b => (0, b)
      map_add' := by intro x y; ext <;> simp
      map_smul' := by
        intro r b
        change (0, r.2 * b) = (r.1 * 0, r.2 * b)
        simp }
  let : Module.Projective (A × B) A := Module.Projective.of_split iA
    (Algebra.linearMap (A × B) A) (by ext; rfl)
  let : Module.Projective (A × B) B := Module.Projective.of_split iB
    (Algebra.linearMap (A × B) B) (by ext; rfl)
  let : Module (A × B) (A ⊗[R] M) :=
    Module.compHom (A ⊗[R] M) (RingHom.fst A B)
  let : Module (A × B) (B ⊗[R] M) :=
    Module.compHom (B ⊗[R] M) (RingHom.snd A B)
  let : @IsScalarTower (A × B) A (A ⊗[R] M)
      (inferInstance : Algebra (A × B) A).toSMul
      (inferInstance : Module A (A ⊗[R] M)).toSMul
      (inferInstance : Module (A × B) (A ⊗[R] M)).toSMul := by
    constructor
    intro r a x
    change (r.1 * a) • x = r.1 • (a • x)
    exact mul_smul r.1 a x
  let : @IsScalarTower (A × B) B (B ⊗[R] M)
      (inferInstance : Algebra (A × B) B).toSMul
      (inferInstance : Module B (B ⊗[R] M)).toSMul
      (inferInstance : Module (A × B) (B ⊗[R] M)).toSMul := by
    constructor
    intro r b x
    change (r.2 * b) • x = r.2 • (b • x)
    exact mul_smul r.2 b x
  let : Module.Projective (A × B) (A ⊗[R] M) :=
    projective_restrictScalars_of_projective_algebra (A × B) A (A ⊗[R] M)
  let : Module.Projective (A × B) (B ⊗[R] M) :=
    projective_restrictScalars_of_projective_algebra (A × B) B (B ⊗[R] M)
  let E : ((A × B) ⊗[R] M) ≃ₗ[A × B] (A ⊗[R] M) × (B ⊗[R] M) :=
    { (TensorProduct.prodLeft R R A B M).toAddEquiv with
      map_smul' := by
        intro r x
        induction x using TensorProduct.inductionOn with
        | tmul a m => rfl
        | add x y hx hy =>
            change (TensorProduct.prodLeft R R A B M) (r • (x + y)) =
              r • (TensorProduct.prodLeft R R A B M) (x + y)
            change (TensorProduct.prodLeft R R A B M) (r • x) =
              r • (TensorProduct.prodLeft R R A B M) x at hx
            change (TensorProduct.prodLeft R R A B M) (r • y) =
              r • (TensorProduct.prodLeft R R A B M) y at hy
            simp only [smul_add, map_add, hx, hy] }
  exact Module.Projective.of_equiv' E.symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
