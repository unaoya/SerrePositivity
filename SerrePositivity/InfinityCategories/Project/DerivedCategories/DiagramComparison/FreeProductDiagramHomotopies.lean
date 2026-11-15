module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramMaps

/-!
概要：元の図式 AW・shuffle の両合成の鎖ホモトピーを指定する。
方針：既存の図式 EZ 同値と、その前向き・逆向き射の照合を使う。
規約：図式圏内のホモトピーであり、各点の存在を選び直さない。
使われ方：HA 1.2.4、IS-W2 §73 A01。全パラメータ Hom 比較の入力。
-/
@[expose] public noncomputable section
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A] {J : Type v} [Category.{w} J]
variable (φ : simplicialRingCoefficient.{u} →+* A) (X Y : J ⥤ SSet.{u})
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)

/-- 指定 AW の後に指定 shuffle を合成すると、図式として恒等射にホモトピック。 -/
def freeProductDiagramAWShuffleHomotopy :
    Homotopy ((E).map (freeProductDiagramAW φ X Y ≫ freeProductDiagramShuffle φ X Y))
      (𝟙 ((E).obj (freeNegativeChainsDiagram (A := A) (X ⊗ Y)))) := by
  rw [CategoryTheory.Functor.map_comp,
    ← freeProductDiagramEZEquiv_hom, ← freeProductDiagramEZEquiv_inv]
  exact (freeProductDiagramEZEquiv φ X Y).homotopyHomInvId

/-- 指定 shuffle の後に指定 AW を合成すると、図式として恒等射にホモトピック。 -/
def freeProductDiagramShuffleAWHomotopy :
    Homotopy ((E).map (freeProductDiagramShuffle φ X Y ≫ freeProductDiagramAW φ X Y))
      (𝟙 ((E).obj (freeNegativeChainsDiagram (A := A) X ⊗
        freeNegativeChainsDiagram (A := A) Y))) := by
  rw [CategoryTheory.Functor.map_comp,
    ← freeProductDiagramEZEquiv_inv, ← freeProductDiagramEZEquiv_hom]
  exact (freeProductDiagramEZEquiv φ X Y).homotopyInvHomId

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
