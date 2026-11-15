module

public import SerrePositivity.AlgebraicGeometry.FinitePresentationCoefficientModel
public import SerrePositivity.AlgebraicGeometry.AffineTensorModelPullback

/-!
概要：係数環を保つ有限表示の affine 模型と、元の Spec の Cartesian な比較。
方針：代数の tensor 模型を既存の Spec の pullback 比較へ渡す。
規約：固有性の有限段への降下は含めない。
使われ方：G2 の有限型 F_p の affine 局所。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u v

/-- 指定した Noether 係数環を保ち、有限表示 affine 射の実際の Cartesian な模型を取る。 -/
theorem exists_affine_finitePresentation_coefficient_model
    (k : Type v) (R S : Type u) [CommRing k] [IsNoetherianRing k]
    [CommRing R] [Algebra k R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] :
    ∃ A : Subalgebra k R, A.FG ∧ IsNoetherianRing A ∧
      ∃ (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra A S₀),
        Algebra.FinitePresentation A S₀ ∧
        ∃ a : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of S₀),
          IsPullback a (Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (Spec.map (CommRingCat.ofHom (algebraMap A S₀)))
            (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  obtain ⟨A, hA, hN, S₀, _, _, hS₀, ⟨e⟩⟩ :=
    exists_finitePresentation_model_over_noetherian_coefficients k R S
  exact ⟨A, hA, hN, S₀, inferInstance, inferInstance, hS₀,
    _, isPullback_affineTensorModel e⟩

end SerrePositivity.AlgebraicGeometry
