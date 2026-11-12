module
public import SerrePositivity.KST.Fibration.KanEnrichedEdgewisePointHom
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.KanEnrichedOppositePointHom
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.KanEnrichedEdgewiseDoubleEvaluation

/-! # 元の大域的な係数反転同型の同じ指定成分と、元の係数点の作用 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J)

/-- 元の大域的反転同型の同じ成分は、元の左右指定成分の合成に厳密に一致する。 -/
theorem kanEnrichedOppositeComponentIso_eq_edgewise (X : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) (j : J) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanEnrichedOppositeComponentIso D X j = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanEnrichedEdgewisePointIso D X j := by
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDoubleEvaluation X j
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map D.edgewiseRightRealizationIso T
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map D.edgewiseLeftRealizationIso T
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map D.oppositeRealizationIso T = R.symm ≪≫ L := by
    simp only [R, L, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.oppositeRealizationIso, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map,
      Functor.mapIso_trans, Functor.mapIso_symm]
  have hn := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints_span R L rfl
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDoubleEvaluation_vertex D.edgewise X j))
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDoubleEvaluation_vertex D.edgewise X j))
    (congrArg HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDoubleEvaluation_precomp_vertex D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedRight C) X j))
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDoubleEvaluation_vertex D.opposite X j)) rfl
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanEnrichedOppositeComponentIso, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanEnrichedEdgewisePointIso,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanEnrichedEdgewiseRightComponent_eq_doubleMap,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanEnrichedEdgewiseLeftComponent_eq_doubleMap]
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map D.oppositeRealizationIso T) _ _ = _
  rw [hm]
  simpa only [eqToIso_refl, Iso.refl_trans] using hn.symm

/-- 元の大域的反転同型の同じ指定成分は、元の点を反転側の同じ点へ送る。 -/
theorem kanEnrichedOppositeComponentIso_pointHom (X : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) (j : J)
    (v : ((D.obj j).obj X.val).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv ((D.obj j).obj X.val)).symm v) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanEnrichedOppositeComponentIso D X j).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj ((D.obj j).obj X.val))).symm
        (SSet.opObjEquiv.symm v)) := by
  rw [kanEnrichedOppositeComponentIso_eq_edgewise]
  exact kanEnrichedEdgewisePointIso_pointHom D X j v

end SerrePositivity.KST.Fibration
