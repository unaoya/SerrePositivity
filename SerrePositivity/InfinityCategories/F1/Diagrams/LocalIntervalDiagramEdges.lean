module

public import SerrePositivity.InfinityCategories.F1.Diagrams.LocalQCatDiagramStrictification
public import SerrePositivity.InfinityCategories.F1.Categories.QCatDiagramEdges
public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramMappingNaturality

/-!
概要：一次元の底の同型は元の二頂点と同じ辺を保持する。
方針：標準単体と有限鎖の nerve の同型を各対象で計算する。
規約：quasicategory 値図式の元の射を別の代表へ置き換えない。
使われ方：三辺固定の正方形から、同じ二辺の合成三角形を取り出す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 底を標準区間へ戻す同型は、指定した同じ頂点を保持する。 -/
lemma localIntervalDiagramBaseIso_vertex (i : Fin 2) :
    (localKanDiagramBaseIso.{u} 1).hom.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i) =
    ULift.up (nerveVertex (ULift.up i : ULift.{u} (Fin 2))) := by
  apply ULift.ext
  apply CategoryTheory.Functor.ext (fun j => ?_)
  rfl

/-- 指定した同じ頂点での側辺は、底の同型を通しても同じ定値な底の側辺。 -/
lemma localIntervalDiagramBaseIso_side (i : Fin 2) :
    lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const (stdSimplex.obj₀Equiv.symm i)) ≫
      (Δ[1] ◁ (localKanDiagramBaseIso.{u} 1).hom) =
    lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (ULift.up (nerveVertex (ULift.up i : ULift.{u} (Fin 2))))) := by
  have h : (SSet.const (stdSimplex.obj₀Equiv.symm i) :
      (Δ[1] : SSet.{u + 1}) ⟶ Δ[1]) ≫ (localKanDiagramBaseIso.{u} 1).hom =
      SSet.const (ULift.up (nerveVertex (ULift.up i : ULift.{u} (Fin 2)))) := by
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
    SSet.yonedaEquiv (localKanDiagramBaseIso.{u} 1).hom =
      ULift.up (nerve.edgeMk strictIntervalIndexArrow).edge := by
  apply ULift.ext
  apply CategoryTheory.Functor.ext (fun i => ?_)
  fin_cases i <;> rfl

/-- 元の一次元 QCat 値図式を標準区間に戻すと、元の輸送射の coherent な辺そのもの。 -/
lemma localQCatIntervalDiagram_edge (D : ULift.{u} (Fin 2) ⥤ QCat.{u}) :
    (localKanDiagramBaseIso.{u} 1).hom ≫ qCatDiagramCoherentNerve D =
      SSet.yonedaEquiv.symm (coherentNerveEdge (D.map strictIntervalIndexArrow)).edge := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, localIntervalDiagramBaseIso_edge,
    qCatDiagramCoherentNerve_edge]
  exact (SSet.yonedaEquiv.apply_symm_apply _).symm

end SerrePositivity.InfinityCategories
