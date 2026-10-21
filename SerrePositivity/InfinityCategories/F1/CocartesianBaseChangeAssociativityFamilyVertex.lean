module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityFamily
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityDiagram
public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramRealizationVertices

/-!
概要：既存の結合比較の全 fibration の族を一対象で固定すると、同じ積上の結合図式になる。
方針：同じ arrow 図式の対象と全ての射を、既存の自然変換の uncurry と照合する。
規約：底全体の元の図式と区間族を保持する。
使われ方：元の結合区間族の辺と分類された結合同型の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C))

/-- 同じ結合比較の arrow 図式の一対象での値は、既存の自然変換の積上の図式そのもの。 -/
lemma cocartesianBaseChangeAssociativityArrow_value :
    quasicategoryDiagramValueFunctor
      (QuasicategoryEnrichedDiagram.toCoreEnrichedFunctor
        (cocartesianBaseChangeAssociativityDiagramComparison l k).arrowDiagram |>.obj p) =
    qCatDiagramArrow (cocartesianBaseChangeAssociativityQCat p.val.hom l k) := by
  refine CategoryTheory.Functor.ext (fun ⟨i, a⟩ ↦ by fin_cases i <;> rfl) ?_
  rintro ⟨i, a⟩ ⟨j, b⟩ f
  fin_cases i <;> fin_cases j
  all_goals simp only [eqToHom_refl, Category.comp_id]
  all_goals rfl

/-- 既存の結合族を元の fibration に固定すると、同じ積上の図式全体の頂点を回収する。 -/
lemma cocartesianBaseChangeAssociativityFamily_vertex :
    (cocartesianBaseChangeAssociativityFamily l k).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex p) =
    functorVertex (qCatDiagramCoherentNerve
      (qCatDiagramArrow (cocartesianBaseChangeAssociativityQCat p.val.hom l k))) := by
  have h := QuasicategoryEnrichedDiagram.realization_vertex
    (cocartesianBaseChangeAssociativityDiagramComparison l k).arrowDiagram p
  have hv := congrArg (fun F ↦ functorVertex (qCatDiagramCoherentNerve F))
    (cocartesianBaseChangeAssociativityArrow_value l k p)
  exact h.trans hv

end SerrePositivity.InfinityCategories
