module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramEvaluationFrames
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryTensor

/-!
概要：指定source frameのHomに、Reedy標的の相対horn・境界充填を適用する。
方針：既存のhorn tensorとboundary tensorの充填性を同じ図式圏で使う。
規約：coherent endへの比較射の弱同値性は、この宣言だけからは主張しない。
使われ方：Hovey §5.4、HTT 4.2.4.4のRR02で用いる相対充填の入力。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open scoped SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance relativeFrameModel : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance relativeFrameInitial : HasInitial (StrictComplexDiagram A d) :=
  (isZero_zero (StrictComplexDiagram A d)).isInitial.hasInitial

/-- 指定frameのHomは、Reedy標的のfibrationをKan fibrationへ送る。 -/
lemma strictDiagramSourceFrameHom_fibration (X : StrictComplexDiagram A d)
    {Y Z : StrictComplexDiagram A d} (p : Y ⟶ Z) [Fibration p] :
    Fibration ((CosimplicialHom.cosimplicialHom
      (strictDiagramSourceFrame A d X).obj).map p) :=
  HomotopyFunctionComplex.cosimplicialHom_fibration _
    (strictDiagramSourceFrame A d X).cofibrant
    (strictDiagramSourceFrame A d X).homotopicallyConstant p

/-- Reedy自明fibrationに対して、指定frameのHomは全境界の相対充填を持つ。 -/
lemma strictDiagramSourceFrameHom_boundary_lifting (X : StrictComplexDiagram A d)
    {Y Z : StrictComplexDiagram A d} (p : Y ⟶ Z)
    [Fibration p] [WeakEquivalence p] (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{u} n).ι
      ((CosimplicialHom.cosimplicialHom (strictDiagramSourceFrame A d X).obj).map p) :=
  HomotopyFunctionComplex.boundary_lifting_of_reedyCofibrant _ n
    (strictDiagramSourceFrame A d X).cofibrant p

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
