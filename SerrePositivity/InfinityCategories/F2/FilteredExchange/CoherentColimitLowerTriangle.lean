module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitNativeUnitTriangle

/-!
概要：元の下三角形を、標的の元の全空間頂点を厳密に持つ同じ三角形として読む。
方針：標的頂点の等式を型へ反映し、円柱と全二単体を変更しない。
規約：始域の native 単位を保持。使われ方：a6 と同じ標的での指定辺の作用比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の定値図式間の指定円柱を、標的の元の全空間頂点で読む。 -/
def coherentColimitIntervalConstantHomotopy :
    SSet.Homotopy (SSet.const (coherentDiagramTotalCocone F).vertex :
      (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
      (SSet.const (coherentDiagramTotalVertex G)) where
  h := (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H)).h
  h₀ := (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H)).h₀
  h₁ := by
    change SSet.ι₁ ≫ (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H)).h =
      SSet.const (coherentDiagramTotalVertex G)
    exact (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H)).h₁.trans
      (congrArg SSet.const (coherentDiagramTotalCocone_vertex G))
  rel := (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H)).rel

/-- 元の下二単体を、元の標的全空間頂点を厳密に保つ三辺で読む。 -/
def coherentColimitTargetLowerTriangle : FunctorCompositionTriangle
    (coconeTransformationHomotopy (coherentDiagramTotalCocone F))
    (coherentColimitIntervalConstantHomotopy B H) (coherentColimitNativeUnitDiagonal B H) where
  diagram := (coherentColimitUnitLowerTriangle B H).diagram
  face_zero := (coherentColimitUnitLowerTriangle B H).face_zero
  face_one := (coherentColimitUnitLowerTriangle B H).face_one
  face_two := (coherentColimitUnitLowerTriangle B H).face_two

end SerrePositivity.InfinityCategories.F2
