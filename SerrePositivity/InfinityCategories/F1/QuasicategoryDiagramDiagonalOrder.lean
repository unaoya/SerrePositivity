module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramDiagonalFunctor
public import SerrePositivity.InfinityCategories.F1.DiagonalQuasicategoryDiagramEvaluation
public import SerrePositivity.InfinityCategories.F1.CoherentOrderDiagrams

/-!
概要：通常の図式の列の対角 coherent 評価は、同じ通常の対角関手の coherent 表示。
方針：元の混合作用の単位からの射を全次数の定値単体へ移す。
規約：底と変換の全単体について厳密な等式を証明する。
使われ方：自然変換の辺の実現と元の prism の全パラメーターでの照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ通常の図式の列の対角評価は、その同じ対角関手の coherent な表示。 -/
lemma diagonalQuasicategoryDiagramEvaluation_order
    {C J : Type u} [Category.{u} C] [LinearOrder J]
    (A : J ⥤ C) (R : J ⥤ QuasicategoryDiagramCategory C) :
    diagonalQuasicategoryDiagramEvaluation A (enrichedFunctorOfOrderDiagram R) =
      enrichedFunctorOfOrderDiagram (quasicategoryDiagramDiagonalFunctor A R) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij := SimplicialThickening.Path.le (P.obj 0)
  change (diagonalQuasicategoryDiagramHom A (enrichedFunctorOfOrderDiagram R) i j).app n P = _
  erw [diagonalQuasicategoryDiagramHom_of_le A (enrichedFunctorOfOrderDiagram R) i j hij]
  change (quasicategoryDiagramMixedHom (A.map (homOfLE hij)) (R.obj i.as) (R.obj j.as)).app n
      (PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (R.map (homOfLE hij))) n.unop.len) =
    PinchedHom.constant (SimplicialCategory.homEquiv' _ _
      ((quasicategoryDiagramDiagonalFunctor A R).map (homOfLE hij))) n.unop.len
  have h : eHomEquiv SSet.{u}
      ((quasicategoryDiagramDiagonalFunctor A R).map (homOfLE hij)) =
      eHomEquiv SSet.{u} (R.map (homOfLE hij)) ≫
        quasicategoryDiagramMixedHom (A.map (homOfLE hij)) (R.obj i.as) (R.obj j.as) :=
    (eHomEquiv SSet.{u}).apply_symm_apply _
  have h₀ := congrArg (SSet.unitHomEquiv _) h.symm
  exact (pinchedConstant_map
    (quasicategoryDiagramMixedHom (A.map (homOfLE hij)) (R.obj i.as) (R.obj j.as))
    (SimplicialCategory.homEquiv' _ _ (R.map (homOfLE hij))) n.unop.len).trans
      (congrArg (fun v ↦ PinchedHom.constant v n.unop.len) h₀)

end SerrePositivity.InfinityCategories
