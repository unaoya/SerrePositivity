module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoefficientTensorNaturality

/-!
概要：一般係数の負次数 AW・shuffle の両入力に対する自然性。
方針：指定整数 EZ 射の自然性を延長し、同じテンソル比較同型の自然性と合成する。
規約：元の写像を保持し、自然な別の比較への置換をしない。
使われ方：HA 1.2.4、G10 の積重みと全単体 Hom パラメータの照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)
variable {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D')

/-- 同じ負次数 AW は二つの単体的射に自然。 -/
theorem negativeCoefficientAlexanderWhitney_naturality :
    extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight
        (simplicialIntegerTensorMap f g) (integerCoefficientExtension φ)))
        ComplexShape.embeddingDownNat ≫ negativeCoefficientAlexanderWhitney φ C' D' =
      negativeCoefficientAlexanderWhitney φ C D ≫ HomologicalComplex.tensorHom
        (extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight f
          (integerCoefficientExtension φ))) ComplexShape.embeddingDownNat)
        (extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight g
          (integerCoefficientExtension φ))) ComplexShape.embeddingDownNat) := by
  let T := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)
  have h := congrArg T.map
    (mappedNormalizedAlexanderWhitney_naturality (integerCoefficientExtension φ) f g)
  simp only [Functor.map_comp] at h
  dsimp only [negativeCoefficientAlexanderWhitney]
  rw [← Category.assoc]
  erw [h]
  rw [Category.assoc]
  erw [negativeMooreTensorCoefficientIso_naturality φ f g]
  simp only [Category.assoc]
  rfl

/-- 同じ負次数 shuffle は二つの単体的射に自然。 -/
theorem negativeCoefficientShuffle_naturality :
    HomologicalComplex.tensorHom
        (extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight f
          (integerCoefficientExtension φ))) ComplexShape.embeddingDownNat)
        (extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight g
          (integerCoefficientExtension φ))) ComplexShape.embeddingDownNat) ≫
        negativeCoefficientShuffle φ C' D' =
      negativeCoefficientShuffle φ C D ≫
        extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight
          (simplicialIntegerTensorMap f g) (integerCoefficientExtension φ)))
          ComplexShape.embeddingDownNat := by
  let T := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)
  have h := congrArg T.map
    (mappedNormalizedShuffle_naturality (integerCoefficientExtension φ) f g)
  simp only [Functor.map_comp] at h
  apply (cancel_epi (negativeMooreTensorCoefficientIso φ C D).hom).1
  dsimp only [negativeCoefficientShuffle]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← negativeMooreTensorCoefficientIso_naturality_assoc]
  simp only [Iso.hom_inv_id_assoc]
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
