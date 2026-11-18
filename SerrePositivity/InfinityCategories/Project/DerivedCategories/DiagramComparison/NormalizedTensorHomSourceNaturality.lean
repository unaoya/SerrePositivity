module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomSourceMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeFrameWeightMaps
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedHomTargetNaturality
/-!
概要：元の自由テンソルHom同型の重み変数の自然性。
方針：同じ標準パラメータ同型の交換則と既存の転置の始域自然性を使う。
規約：A11の前提計算1/3。同じ自由テンソル同型と重み射を保持する。
使われ方：HA 1.2.4、元の指定比較の重み変数の自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]
/-- 同じ自由テンソルHom同型は元の重みの全射に自然。 -/
theorem freeTensorDiagramHomIso_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (Q : J ⥤ Complex A) :
    (cosimplicialHomMap (freeTensorFrameWeightMap A w (liftedStandardSimplexParameter J))).app Q ≫
      (freeTensorDiagramHomIso.{u,u} A Q W').hom =
    (freeTensorDiagramHomIso.{u,u} A Q W).hom ≫ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map
      (diagramHomSourceMap.{u,u} ((freeNegativeChainsDiagramFunctor A J).map w) Q) := by
  ext n g
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n.unop
    (diagramTensorLinearHomEquiv.{u,u} (freeNegativeChainsDiagram (A := A) W') Q _
      ((freeTensorStandardSimplexIso A J W').inv.app n.unop ≫
        ((freeTensorFrameWeightMap A w (liftedStandardSimplexParameter J)).app n.unop ≫ g))) =
    ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map
      (diagramHomSourceMap.{u,u} ((freeNegativeChainsDiagramFunctor A J).map w) Q)).app n
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n.unop
        (diagramTensorLinearHomEquiv.{u,u} (freeNegativeChainsDiagram (A := A) W) Q _
          ((freeTensorStandardSimplexIso A J W).inv.app n.unop ≫ g)))
  erw [← _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp]
  apply congrArg (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n.unop)
  have hw : (freeTensorStandardSimplexIso A J W').inv.app n.unop ≫
      (freeTensorFrameWeightMap A w (liftedStandardSimplexParameter J)).app n.unop =
    (((freeNegativeChainsDiagramFunctor A J).map w) ▷
      (Functor.const J).obj ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
        (SSet.stdSimplex.obj n.unop))) ≫ (freeTensorStandardSimplexIso A J W).inv.app n.unop := by
    change (freeNegativeChainsDiagram (A := A) W' ◁ (freeStandardSimplexParameterIso A J).inv.app n.unop) ≫
      (((freeNegativeChainsDiagramFunctor A J).map w) ▷
        (liftedStandardSimplexParameter J ⋙ freeNegativeChainsDiagramFunctor A J).obj n.unop) =
      (((freeNegativeChainsDiagramFunctor A J).map w) ▷
        (Functor.const J).obj ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
          (SSet.stdSimplex.obj n.unop))) ≫
      (freeNegativeChainsDiagram (A := A) W ◁ (freeStandardSimplexParameterIso A J).inv.app n.unop)
    exact whisker_exchange _ _
  rw [← Category.assoc, hw, Category.assoc]
  exact diagramTensorLinearHomEquiv_source _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
