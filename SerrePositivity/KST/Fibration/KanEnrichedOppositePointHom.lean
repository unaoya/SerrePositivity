module
public import SerrePositivity.KST.Fibration.KanEnrichedEdgewisePointHom
public import SerrePositivity.InfinityCategories.Stable.KanModels.KanEnrichedOppositePointHom
public import SerrePositivity.InfinityCategories.Stable.KanModels.KanEnrichedEdgewiseDoubleEvaluation

/-! # 元の大域的な係数反転同型の同じ指定成分と、元の係数点の作用 -/

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

/-- 元の大域的反転同型の同じ成分は、元の左右指定成分の合成に厳密に一致する。 -/
theorem kanEnrichedOppositeComponentIso_eq_edgewise (X : EdgewiseEnrichedObject C) (j : J) :
    kanEnrichedOppositeComponentIso D X j = kanEnrichedEdgewisePointIso D X j := by
  let T := kanEnrichedDoubleEvaluation X j
  let R := VertexIso.map D.edgewiseRightRealizationIso T
  let L := VertexIso.map D.edgewiseLeftRealizationIso T
  have hm : VertexIso.map D.oppositeRealizationIso T = R.symm ≪≫ L := by
    simp only [R, L, KanEnrichedDiagram.oppositeRealizationIso, VertexIso.map,
      Functor.mapIso_trans, Functor.mapIso_symm]
  have hn := F2.isoNormalizeEndpoints_span R L rfl
    (congrArg HomotopyCategory.mk (kanEnrichedDoubleEvaluation_vertex D.edgewise X j))
    (congrArg HomotopyCategory.mk (kanEnrichedDoubleEvaluation_vertex D.edgewise X j))
    (congrArg HomotopyCategory.mk
      (kanEnrichedDoubleEvaluation_precomp_vertex D (edgewiseEnrichedRight C) X j))
    (congrArg HomotopyCategory.mk (kanEnrichedDoubleEvaluation_vertex D.opposite X j)) rfl
  rw [kanEnrichedOppositeComponentIso, kanEnrichedEdgewisePointIso,
    kanEnrichedEdgewiseRightComponent_eq_doubleMap,
    kanEnrichedEdgewiseLeftComponent_eq_doubleMap]
  change F2.isoNormalizeEndpoints (VertexIso.map D.oppositeRealizationIso T) _ _ = _
  rw [hm]
  simpa only [eqToIso_refl, Iso.refl_trans] using hn.symm

/-- 元の大域的反転同型の同じ指定成分は、元の点を反転側の同じ点へ送る。 -/
theorem kanEnrichedOppositeComponentIso_pointHom (X : EdgewiseEnrichedObject C) (j : J)
    (v : ((D.obj j).obj X.val).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv ((D.obj j).obj X.val)).symm v) ≫
      (kanEnrichedOppositeComponentIso D X j).hom =
    cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv (kanObjectOpFunctor.obj ((D.obj j).obj X.val))).symm
        (SSet.opObjEquiv.symm v)) := by
  rw [kanEnrichedOppositeComponentIso_eq_edgewise]
  exact kanEnrichedEdgewisePointIso_pointHom D X j v

end SerrePositivity.KST.Fibration
