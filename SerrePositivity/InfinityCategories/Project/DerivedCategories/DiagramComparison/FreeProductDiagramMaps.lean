module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramEZ
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramExtendNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoefficientDiagramMaps

/-!
概要：自由積図式の同値の射を、各点で指定した元の AW・shuffle と照合する。
方針：係数図式の成分等式と、元の図式交換・零延長比較の自然性を使う。
規約：同値の存在だけでなく同じ射の等式を保持する。
使われ方：HA 1.2.4、G10 の全単体比較と指定豊穣合成の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type v} [Category.{w} J] {A : Type u} [CommRing A]
variable (φ : simplicialRingCoefficient.{u} →+* A) (X Y : J ⥤ SSet.{u})

/-- 元の自由積 AW の全図式射。 -/
def freeProductDiagramAW : freeNegativeChainsDiagram (A := A) (X ⊗ Y) ⟶
    freeNegativeChainsDiagram (A := A) X ⊗ freeNegativeChainsDiagram (A := A) Y where
  app j := freeProductAlexanderWhitney φ (X.obj j) (Y.obj j)
  naturality _ _ f := freeProductAlexanderWhitney_naturality φ (X.map f) (Y.map f)

/-- 元の自由積 shuffle の全図式射。 -/
def freeProductDiagramShuffle :
    freeNegativeChainsDiagram (A := A) X ⊗ freeNegativeChainsDiagram (A := A) Y ⟶
      freeNegativeChainsDiagram (A := A) (X ⊗ Y) where
  app j := freeProductShuffle φ (X.obj j) (Y.obj j)
  naturality _ _ f := freeProductShuffle_naturality φ (X.map f) (Y.map f)

/-- 図式の同値の順方向は元の指定 AW の全図式射である。 -/
theorem freeProductDiagramEZEquiv_hom : (freeProductDiagramEZEquiv φ X Y).hom =
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).map (freeProductDiagramAW φ X Y) := by
  dsimp only [freeProductDiagramEZEquiv, negativeEZDiagramTargetEquiv,
    HomotopyEquiv.trans_hom, HomotopyEquiv.ofIso, Iso.symm_hom, Iso.trans_inv, Iso.trans_hom]
  change _ ≫ (extendMap (coefficientEZDiagramEquiv (integerCoefficientExtension φ)
    (integerLinearizedSpaceDiagram X) (integerLinearizedSpaceDiagram Y)).hom
      ComplexShape.embeddingDownNat ≫ _) ≫ _ = _
  rw [coefficientEZDiagramEquiv_hom]
  simp only [Category.assoc]
  rw [negativeDiagramExchangeIso_naturality_assoc]
  simp only [Iso.inv_hom_id_assoc]
  simp only [CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.mapIso_hom]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  congr 1

/-- 図式の同値の逆方向も元の指定 shuffle の全図式射である。 -/
theorem freeProductDiagramEZEquiv_inv : (freeProductDiagramEZEquiv φ X Y).inv =
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).map (freeProductDiagramShuffle φ X Y) := by
  simp only [freeProductDiagramEZEquiv, negativeEZDiagramTargetEquiv,
    HomotopyEquiv.trans_inv, HomotopyEquiv.ofIso, Iso.symm_inv, Iso.trans_inv, Iso.trans_hom,
    negativeCoefficientEZDiagramEquiv]
  rw [coefficientEZDiagramEquiv_inv]
  simp only [Category.assoc]
  rw [negativeDiagramExchangeIso_naturality_assoc]
  simp only [Iso.inv_hom_id_assoc]
  simp only [CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.mapIso_hom]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  congr 1

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
