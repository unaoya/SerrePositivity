module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialNerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagram
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramEdgewise
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramOppositeComparison
public import SerrePositivity.InfinityCategories.F1.KanModels.KanOppositeCoefficients
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedCategory
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedComparison
public import SerrePositivity.InfinityCategories.F1B.IsoEndpointNormalization
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDoubleEvaluation

/-!
分割で生成：docstring を書き直すこと
 # 元の大域的な係数反転同型の同じ指定成分と、元の係数点の作用
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J)

/-- 元の大域的反転同型を同じ二重評価で写し、元の二つの Kan 値へ端点だけを揃える。 -/
def kanEnrichedOppositeComponentIso (X : EdgewiseEnrichedObject C) (j : J) :
    VertexIso (spaceInfinityVertex ((D.obj j).obj X.val))
      (spaceInfinityVertex (kanObjectOpFunctor.obj ((D.obj j).obj X.val))) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map D.oppositeRealizationIso (kanEnrichedDoubleEvaluation X j))
    (congrArg HomotopyCategory.mk
      (kanEnrichedDoubleEvaluation_precomp_vertex D (edgewiseEnrichedRight C) X j))
    (congrArg HomotopyCategory.mk (kanEnrichedDoubleEvaluation_vertex D.opposite X j))

end SerrePositivity.KST.Fibration
