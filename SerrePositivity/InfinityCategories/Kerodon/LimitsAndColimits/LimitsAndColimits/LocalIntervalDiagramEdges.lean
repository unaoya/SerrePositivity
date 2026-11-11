module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalQCatDiagramStrictification
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatDiagramEdges
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.StrictDiagramMappingNaturality

/-!
概要：一次元の底の同型は元の二頂点と同じ辺を保持する。
方針：標準単体と有限鎖の nerve の同型を各対象で計算する。
規約：quasicategory 値図式の元の射を別の代表へ置き換えない。
使われ方：三辺固定の正方形から、同じ二辺の合成三角形を取り出す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 底を標準区間へ戻す同型は、指定した同じ頂点を保持する。 -/
lemma localIntervalDiagramBaseIso_vertex (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).hom.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i) =
    ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up i : ULift.{u} (Fin 2))) := by
  apply ULift.ext
  apply CategoryTheory.Functor.ext (fun j => ?_)
  rfl

/-- 指定した同じ頂点での側辺は、底の同型を通しても同じ定値な底の側辺。 -/
lemma localIntervalDiagramBaseIso_side (i : Fin 2) :
    lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const (stdSimplex.obj₀Equiv.symm i)) ≫
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).hom) =
    lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up i : ULift.{u} (Fin 2))))) := by
  have h : (SSet.const (stdSimplex.obj₀Equiv.symm i) :
      (Δ[1] : SSet.{u + 1}) ⟶ Δ[1]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).hom =
      SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up i : ULift.{u} (Fin 2)))) := by
    rw [SSet.const_comp, localIntervalDiagramBaseIso_vertex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · rfl
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app h n) s

/-- 底を標準区間へ戻す同型は、元の鎖の同じ非退化辺を保持する。 -/
lemma localIntervalDiagramBaseIso_edge :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).hom =
      ULift.up (nerve.edgeMk _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow).edge := by
  apply ULift.ext
  apply CategoryTheory.Functor.ext (fun i => ?_)
  fin_cases i <;> rfl

/-- 元の一次元 QCat 値図式を標準区間に戻すと、元の輸送射の coherent な辺そのもの。 -/
lemma localQCatIntervalDiagram_edge (D : ULift.{u} (Fin 2) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve D =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (D.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow)).edge := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, localIntervalDiagramBaseIso_edge,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.qCatDiagramCoherentNerve_edge]
  exact (SSet.yonedaEquiv.apply_symm_apply _).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
