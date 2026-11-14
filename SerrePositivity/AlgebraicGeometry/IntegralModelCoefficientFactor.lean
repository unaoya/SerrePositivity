module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIntRingColimitFactor
public import SerrePositivity.AlgebraicGeometry.IntegralModelSpec

/-!
概要：Noether 係数模型の環写像を、整射の有限・有限表示模型の実際の段へ因子化する。
方針：有限型 ℤ-代数の colimit の因子化に I03 の実際の cocone を渡し、反変 Spec を適用する。
規約：新しい模型の存在を仮定しない。I01〜I04 の構造射を使う。
使われ方：A07 の C03 に渡す、同じ有限段で因子化した係数写像。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 有限型 ℤ-係数環の写像を、整射の実際の有限・有限表示模型の段へ因子化する。 -/
theorem exists_integral_model_stage_factor_of_finiteType_int
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (g : A →+* B) :
    ∃ (i : IntegralModelIndex R B) (g₀ : A →+* (integralModelSmallDiagram R B).obj i),
      g = ((integralModelSmallCocone R B).ι.app i).hom.comp g₀ :=
  exists_ringHom_factor_of_finiteType_int (integralModelSmallDiagram R B)
    (integralModelSmallCocone R B) (integralModelSmallCoconeIsColimit R B) A g

set_option backward.isDefEq.respectTransparency false in
/-- 同じ係数の因子化を、I04 の実際の Spec の極限 cone の可換式として返す。 -/
theorem exists_integral_model_spec_factor_of_finiteType_int
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (g : A →+* B) :
    ∃ (i : IntegralModelIndex R B)
      (γ : (integralModelSpecDiagram R B).obj (.op i) ⟶ Spec (CommRingCat.of A)),
      (integralModelSpecCone R B).π.app (.op i) ≫ γ = Spec.map (CommRingCat.ofHom g) := by
  obtain ⟨i, g₀, hg⟩ := exists_integral_model_stage_factor_of_finiteType_int R B A g
  refine ⟨i, Spec.map (CommRingCat.ofHom g₀), ?_⟩
  rw [integralModelSpecCone_projection, ← Spec.map_comp]
  congr 1
  ext x
  exact DFunLike.congr_fun hg.symm x

end SerrePositivity.AlgebraicGeometry
