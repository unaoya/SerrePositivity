module

public import SerrePositivity.AlgebraicGeometry.QuotientModuleBaseChange
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：KST §5、Stacks 05FS の射影的な最初の剰余の任意の基底変更。
方針：商環へのテンソル比較と二回の取消で、元の剰余のテンソル基底変更と同定する。
規約：係数変更の平坦性・完備性を要求しない。
使われ方：完備化後の代数の剰余の射影性を元の剰余から用意する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：射影的な剰余を持つ加群は、任意の係数変更後も拡大イデアルによる剰余が射影的。
方針：商テンソル同型と基底変更の取消で、射影加群のテンソル基底変更へ移す。
規約：KST §5、Stacks 05FS、同型は新しい商環上の線形同型。
使われ方：完備基底上での幾何学的整な代数の射影性判定。
-/
theorem projective_reduction_baseChange
    {R C M : Type u} [CommRing R] [CommRing C] [Algebra R C]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Projective (C ⧸ I.map (algebraMap R C))
      ((C ⊗[R] M) ⧸
        ((I.map (algebraMap R C)) • (⊤ : Submodule C (C ⊗[R] M)))) := by
  let J := I.map (algebraMap R C)
  let K := C ⧸ J
  let : Algebra (R ⧸ I) K :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R (R ⧸ I) K :=
    IsScalarTower.of_algebraMap_eq' rfl
  let E₀ := quotientModuleTensorEquiv J (C ⊗[R] M)
  let E₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange R C K K M
  let E₂ := (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
    (quotientModuleTensorEquiv I M).symm) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) K K M
  exact Module.Projective.of_equiv' (E₂ ≪≫ₗ E₁.symm ≪≫ₗ E₀)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
