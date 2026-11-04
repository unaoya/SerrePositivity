module
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.Opposite
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagram
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramComparison
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramEdgewise
public import SerrePositivity.InfinityCategories.F1.KanModels.KanOppositeCoefficients
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedSpaceFiberVertices
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEndpoints
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedCategory
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedComparison
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseLeftFilling
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseRightFilling
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseSubdivision
public import SerrePositivity.InfinityCategories.F1.Transport.CosliceTransportPointHom
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedRealizationPointHom

/-!
分割で生成：docstring を書き直すこと
 # 同じ edgewise 共同比較の左右の指定成分で、元の係数点を反転側へ追跡する
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

/-- 元の共同実現の右比較から取り出した、同じ指定成分。 -/
def kanEnrichedEdgewiseRightComponent (X : EdgewiseEnrichedObject C) (j : J) :
    VertexIso (spaceInfinityVertex ((D.edgewise.obj j).obj X))
      (spaceInfinityVertex ((D.obj j).obj X.val)) :=
  kanEnrichedRealizationComponentIso D.edgewiseRightComparison
    (fun k Y => isQCatEquivalence_of_trivialKanFibration
      (edgewiseRight ((D.obj k).obj Y.val).obj)) X j

/-- 同じ共同実現の左比較から取り出した、同じ指定成分。 -/
def kanEnrichedEdgewiseLeftComponent (X : EdgewiseEnrichedObject C) (j : J) :
    VertexIso (spaceInfinityVertex ((D.edgewise.obj j).obj X))
      (spaceInfinityVertex (kanObjectOpFunctor.obj ((D.obj j).obj X.val))) :=
  kanEnrichedRealizationComponentIso D.edgewiseLeftComparison
    (fun k Y => isQCatEquivalence_of_trivialKanFibration
      (edgewiseLeft ((D.obj k).obj Y.val).obj)) X j

/-- 同じ右成分の逆と同じ左成分を合成し、比較を再選択せず係数反転を得る。 -/
def kanEnrichedEdgewisePointIso (X : EdgewiseEnrichedObject C) (j : J) :
    VertexIso (spaceInfinityVertex ((D.obj j).obj X.val))
      (spaceInfinityVertex (kanObjectOpFunctor.obj ((D.obj j).obj X.val))) :=
  (kanEnrichedEdgewiseRightComponent D X j).symm ≪≫
    kanEnrichedEdgewiseLeftComponent D X j

/-- 元の共通係数点の右端と左端は、同じ二つの指定成分の合成で対応する。 -/
theorem kanEnrichedEdgewisePointIso_endpoints (X : EdgewiseEnrichedObject C) (j : J)
    (w : (edgewiseSubdivision ((D.obj j).obj X.val).obj) _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv ((D.obj j).obj X.val)).symm
      ((edgewiseRight ((D.obj j).obj X.val).obj).app (Opposite.op ⦋0⦌) w)) ≫
        (kanEnrichedEdgewisePointIso D X j).hom =
    cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv (kanObjectOpFunctor.obj ((D.obj j).obj X.val))).symm
        ((edgewiseLeft ((D.obj j).obj X.val).obj).app (Opposite.op ⦋0⦌) w)) := by
  have hr := kanEnrichedRealizationComponentIso_pointHom D.edgewiseRightComparison
    (fun k Y => isQCatEquivalence_of_trivialKanFibration
      (edgewiseRight ((D.obj k).obj Y.val).obj)) X j w
  have hl := kanEnrichedRealizationComponentIso_pointHom D.edgewiseLeftComparison
    (fun k Y => isQCatEquivalence_of_trivialKanFibration
      (edgewiseLeft ((D.obj k).obj Y.val).obj)) X j w
  change cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((D.edgewise.obj j).obj X)).symm w) ≫
        (kanEnrichedEdgewiseRightComponent D X j).hom =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv ((D.obj j).obj X.val)).symm
      ((edgewiseRight ((D.obj j).obj X.val).obj).app (Opposite.op ⦋0⦌) w)) at hr
  change cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((D.edgewise.obj j).obj X)).symm w) ≫
        (kanEnrichedEdgewiseLeftComponent D X j).hom =
    cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv (kanObjectOpFunctor.obj ((D.obj j).obj X.val))).symm
        ((edgewiseLeft ((D.obj j).obj X.val).obj).app (Opposite.op ⦋0⦌) w)) at hl
  change _ ≫ (kanEnrichedEdgewiseRightComponent D X j).inv ≫
    (kanEnrichedEdgewiseLeftComponent D X j).hom = _
  rw [← hr, Category.assoc, Iso.hom_inv_id_assoc]
  exact hl

end SerrePositivity.KST.Fibration
