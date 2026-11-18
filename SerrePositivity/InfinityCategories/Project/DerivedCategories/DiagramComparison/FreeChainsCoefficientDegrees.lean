module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeChainsCoefficientProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedAWRightAugmentationCut
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductFrameCoaction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentation
/-!
概要：指定AWの最後の切断の右余単位則。
方針：係数移送の純テンソルを評価する。規約：IS-W2 A05aの証明の分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open AlgebraicTopology AlgebraicTopology.DoldKan HomologicalComplex
open SerrePositivity.HomologicalAlgebra
open scoped Simplicial TensorProduct
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 同じ射影の負次数成分。 -/
theorem freeChainsCoefficient_degree {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A) (X : SSet.{u}) (r : ℕ) :
    (integerCoefficientExtension φ).map ((PInftyToNormalizedMooreComplex (linearizedSpace X)).f r) ≫
      (((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
        ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv) ≫
      (extendMap (normalizedMooreMapHom (integerCoefficientExtension φ) (linearizedSpace X)) ComplexShape.embeddingDownNat ≫
        (integerCoefficientFreeChainsIso φ X).hom).f (-(r : ℤ)) =
    (integerCoefficientSimplicialFreeIso φ X).hom.app (Opposite.op ⦋r⦌) ≫
      (PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)).f r ≫
      (((normalizedMooreComplex (ModuleCat A)).obj (X ⋙ ModuleCat.free A)).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv := by
  dsimp only [integerCoefficientFreeChainsIso, Functor.mapIso_hom,
    ComplexShape.Embedding.extendFunctor]
  simp only [comp_f]
  erw [extendMap_f _ _ (i := r) rfl, extendMap_f _ _ (i := r) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h := congrArg (fun f => f.f r) (freeChainsCoefficient_projection φ X)
  change (integerCoefficientExtension φ).map ((PInftyToNormalizedMooreComplex (linearizedSpace X)).f r) ≫
    (normalizedMooreMapHom (integerCoefficientExtension φ) (linearizedSpace X)).f r ≫
    ((normalizedMooreComplex (ModuleCat A)).map
      (integerCoefficientSimplicialFreeIso φ X).hom).f r =
    𝟙 _ ≫ (integerCoefficientSimplicialFreeIso φ X).hom.app (Opposite.op ⦋r⦌) ≫
      (PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)).f r at h
  simp only [Category.id_comp] at h
  erw [reassoc_of% h]
/-- 同じ射影を自由生成元に評価した式。 -/
theorem freeChainsCoefficient_generator_value {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A) (X : SSet.{u}) (r : ℕ) (a : X.obj (Opposite.op ⦋r⦌)) :
    ((integerCoefficientFreeChainsIso φ X).hom.f (-(r : ℤ)))
      ((extendMap (normalizedMooreMapHom (integerCoefficientExtension φ) (linearizedSpace X))
        ComplexShape.embeddingDownNat).f (-(r : ℤ))
        ((((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
            ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv)
          ((integerCoefficientExtension φ).map
            ((PInftyToNormalizedMooreComplex (linearizedSpace X)).f r)
            ((integerCoefficientFreeAdjunction φ).unit.app _ a)))) =
    (((normalizedMooreComplex (ModuleCat A)).obj (X ⋙ ModuleCat.free A)).extendXIso
      ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
      ((PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)).f r (ModuleCat.freeMk a)) := by
  have h := congrArg (fun f => f ((integerCoefficientFreeAdjunction φ).unit.app _ a)) (freeChainsCoefficient_degree φ X r)
  simp only [comp_f, ModuleCat.comp_apply] at h
  erw [integerCoefficientFreeIso_generator] at h
  exact h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
