module
public import SerrePositivity.InfinityCategories.Stable.KanModels.KanEnrichedEdgewisePointHom
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedRealizationPointHom
public import SerrePositivity.KST.Fibration.EdgewiseDiagonalPoint

/-! # 同じ edgewise 共同比較の左右の指定成分で、元の係数点を反転側へ追跡する -/

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

/-- 元の係数点の退化辺を使うと、同じ指定成分が反転した同じ点の射を回収する。 -/
theorem kanEnrichedEdgewisePointIso_pointHom (X : EdgewiseEnrichedObject C) (j : J)
    (v : ((D.obj j).obj X.val).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv ((D.obj j).obj X.val)).symm v) ≫
      (kanEnrichedEdgewisePointIso D X j).hom =
    cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv (kanObjectOpFunctor.obj ((D.obj j).obj X.val))).symm
        (SSet.opObjEquiv.symm v)) := by
  simpa only [edgewiseDiagonalPoint_right, edgewiseDiagonalPoint_left] using
    kanEnrichedEdgewisePointIso_endpoints D X j
      (edgewiseDiagonalPoint ((D.obj j).obj X.val).obj v)

end SerrePositivity.KST.Fibration
