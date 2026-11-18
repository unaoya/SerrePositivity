module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomTargetMap
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedHomTargetNaturality
/-!
概要：元の自由テンソルHom同型の標的変数への自然性。
方針：既存テンソル–Homの標的自然性と元のΓの標的自然性を合成する。
規約：A10の前提計算1/3。同じ自由テンソル同型と図式射を保持する。
使われ方：HA 1.2.4、指定正規化重み比較の全図式射自然性。
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
variable (W : J ⥤ SSet.{u})
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)
/-- 指定された自由テンソルHom同型は標的の全図式射に自然。 -/
theorem freeTensorDiagramHomIso_target_naturality {Q Q' : J ⥤ Complex A} (f : Q ⟶ Q') :
    (cosimplicialHom (freeTensorFrame A W (liftedStandardSimplexParameter J))).map f ≫
      (freeTensorDiagramHomIso.{u,u} A Q' W).hom =
    (freeTensorDiagramHomIso.{u,u} A Q W).hom ≫ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map
      (diagramHomTargetMap.{u,u} (freeNegativeChainsDiagram (A := A) W) f) := by
  ext n g
  change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n.unop
    (diagramTensorLinearHomEquiv.{u,u} (freeNegativeChainsDiagram (A := A) W) Q' _
      ((freeTensorStandardSimplexIso A J W).inv.app n.unop ≫ (g ≫ f))) =
    ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map
      (diagramHomTargetMap.{u,u} (freeNegativeChainsDiagram (A := A) W) f)).app n
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n.unop
        (diagramTensorLinearHomEquiv.{u,u} (freeNegativeChainsDiagram (A := A) W) Q _
          ((freeTensorStandardSimplexIso A J W).inv.app n.unop ≫ g)))
  erw [← _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp]
  apply congrArg (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n.unop)
  simpa only [Category.assoc] using diagramTensorLinearHomEquiv_postcomp.{u,u}
    (freeNegativeChainsDiagram (A := A) W)
    ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n.unop))
    ((freeTensorStandardSimplexIso A J W).inv.app n.unop ≫ g) f
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
