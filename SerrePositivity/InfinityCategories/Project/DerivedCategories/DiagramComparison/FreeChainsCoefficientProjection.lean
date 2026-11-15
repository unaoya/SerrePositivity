module
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreMapProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductEZ
/-!
概要：係数移送後の指定Moore射影を、元の自由化の射影へ接続する。
方針：Moore比較の射影則と自由化比較の自然性を合成する。
規約：A05aの証明の分割。指定比較を保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 指定係数移送と自由化比較は元のMoore射影を保つ。 -/
@[reassoc]
theorem freeChainsCoefficient_projection {A : Type u} [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A) (X : SSet.{u}) :
    ((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).map
        (PInftyToNormalizedMooreComplex (linearizedSpace X)) ≫
      normalizedMooreMapHom (integerCoefficientExtension φ) (linearizedSpace X) ≫
      (normalizedMooreComplex (ModuleCat A)).map
        (integerCoefficientSimplicialFreeIso φ X).hom =
    (alternatingFaceMapComplexCompMapHomologicalComplexIso
      (integerCoefficientExtension φ)).hom.app (linearizedSpace X) ≫
      (alternatingFaceMapComplex (ModuleCat A)).map
        (integerCoefficientSimplicialFreeIso φ X).hom ≫
      PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A) := by
  rw [normalizedMooreMapHom_projection_assoc]
  erw [← PInftyToNormalizedMooreComplex_naturality]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
