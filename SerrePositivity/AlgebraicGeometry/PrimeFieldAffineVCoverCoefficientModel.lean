module

public import SerrePositivity.AlgebraicGeometry.AffineVCoverCoefficientModel
public import Mathlib.Algebra.Field.ZMod

/-!
概要：有限表示 affine v 被覆を、有限型 F_p 上の実際の被覆模型にする。
方針：Noether な係数環上の模型を特殊化し、模型の始域の F_p 構造を明示する。
規約：指定した F_p 構造と tensor 同型を保ち、零環も許す。
使われ方：B03 の有限表示側の有限型 F_p への帰着。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u

/-- 有限表示 affine v 被覆には、両環とも有限型 F_p の実際の被覆模型がある。 -/
theorem exists_primeField_affineVCover_coefficient_model
    (p : ℕ) [Fact p.Prime] (R C : Type u)
    [CommRing R] [Algebra (ZMod p) R] [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C]
    (hf : IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap R C)))) :
    ∃ B : Subalgebra (ZMod p) R, B.FG ∧ Algebra.FiniteType (ZMod p) B ∧
      IsNoetherianRing B ∧ ∃ (C₀ : Type u) (_ : CommRing C₀) (_ : Algebra B C₀)
        (_ : Algebra (ZMod p) C₀),
        IsScalarTower (ZMod p) B C₀ ∧ Algebra.FinitePresentation B C₀ ∧
        Algebra.FiniteType (ZMod p) C₀ ∧
        IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap B C₀))) ∧
        Nonempty (R ⊗[B] C₀ ≃ₐ[R] C) := by
  obtain ⟨B, hB, hN, C₀, _, _, hfp, hv, he⟩ :=
    exists_affineVCover_finitePresentation_coefficient_model (ZMod p) R C hf
  letI : Algebra.FiniteType (ZMod p) B := (Subalgebra.fg_iff_finiteType B).mp hB
  letI : Algebra.FinitePresentation B C₀ := hfp
  letI : Algebra (ZMod p) C₀ :=
    ((algebraMap B C₀).comp (algebraMap (ZMod p) B)).toAlgebra
  letI : IsScalarTower (ZMod p) B C₀ := IsScalarTower.of_algebraMap_eq' rfl
  have ht : Algebra.FiniteType (ZMod p) C₀ := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType (ZMod p) B)
    (inferInstance : Algebra.FiniteType B C₀)
  exact ⟨B, hB, inferInstance, hN, C₀, inferInstance, inferInstance, inferInstance,
    inferInstance, hfp, ht, hv, he⟩

end SerrePositivity.AlgebraicGeometry
