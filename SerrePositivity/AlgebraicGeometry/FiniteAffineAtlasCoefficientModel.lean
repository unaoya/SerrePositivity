module

public import SerrePositivity.AlgebraicGeometry.FiniteAffinePresentationAtlas
public import SerrePositivity.AlgebraicGeometry.FiniteFamilyCoefficientModels
public import SerrePositivity.AlgebraicGeometry.AffineTensorModelPullback

/-!
概要：元の有限表示スキームの全 affine チャートに、共通する係数模型を供給する。
方針：有限アトラスと有限族の係数模型を組み合わせ、同じ tensor 同型で Cartesian 比較を取る。
規約：重なりの模型と貼り合わせの存在は次の工程。
使われ方：G2 の一般の有限表示対象の模型の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- 元の有限表示スキームの全チャートに、共通する有限生成係数環上の実際の Cartesian な模型を取る。 -/
theorem exists_finite_affine_atlas_coefficient_model
    (k : Type v) [CommRing k] [IsNoetherianRing k]
    {R : CommRingCat.{u}} [Algebra k R] {X : Scheme.{u}}
    (f : X ⟶ Spec R) [LocallyOfFinitePresentation f] [QuasiCompact f] :
    ∃ A : Subalgebra k R, A.FG ∧ IsNoetherianRing A ∧
      ∃ (n : ℕ) (B : Fin n → CommRingCat.{u}) (b : ∀ i, R ⟶ B i)
        (a : ∀ i, Spec (B i) ⟶ X),
        (∀ i, IsOpenImmersion (a i) ∧ (b i).hom.FinitePresentation ∧ a i ≫ f = Spec.map (b i)) ∧
        (∀ x : X, ∃ i z, a i z = x) ∧
        ∀ i, ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
          Algebra.FinitePresentation A C ∧
          ∃ h : Spec (B i) ⟶ Spec (CommRingCat.of C),
            IsPullback h (Spec.map (b i))
              (Spec.map (CommRingCat.ofHom (algebraMap A C)))
              (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  obtain ⟨n, B, b, a, hB, hcover⟩ := exists_finite_affine_presentation_atlas f
  letI (i : Fin n) : Algebra R (B i) := (b i).hom.toAlgebra
  haveI (i : Fin n) : Algebra.FinitePresentation R (B i) := (hB i).2.1
  obtain ⟨A, hA, hN, hC⟩ := exists_common_finitePresentation_coefficient_models k R (fun i ↦ B i)
  refine ⟨A, hA, hN, n, B, b, a, hB, hcover, ?_⟩
  intro i
  obtain ⟨C, _, _, hfp, ⟨e⟩⟩ := hC i
  exact ⟨C, inferInstance, inferInstance, hfp, _, isPullback_affineTensorModel e⟩

end SerrePositivity.AlgebraicGeometry
