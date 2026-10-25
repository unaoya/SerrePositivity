module

public import SerrePositivity.InfinityCategories.F2.Ind.FinitePosetEvaluationCofinality

/-!
概要：元の有限半順序全図式そのものは、小さい単一 κ-filtered Yoneda 表示を持つ。
方針：元の実表示 comma の filtered 性と全指定点評価の共終性を標準全余錐へ適用する。
規約：元の全図式を厳密な頂点とする同じ標準余錐を用いる。
使われ方：I-2 a の公開結論、Ind の有限余極限と有限極限の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {P : Type u} [PartialOrder P] [Finite P]
  {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ IndInfinity κ C)

/-- 概要：元の小さい表示添字の全指定点評価自身は right cofinal。
方針：小さい実模型同型を合成。規約：同じ評価。使われ方：標準全余錐の普遍性。 -/
lemma smallDiagramCommaEvaluation_finitePoset_isRightCofinal (k : (nerve P) _⦋0⦌) :
    IsRightCofinal (smallDiagramCommaEvaluation κ D k) :=
  (isRightCofinal_of_isIso (smallDiagramCommaIso κ D).hom).comp
    (diagramCommaEvaluation_finitePoset_isRightCofinal κ D k)

/-- 概要：元の有限半順序図式を頂点とする同じ標準全余錐は余極限錐。
方針：全指定点の共終性。規約：元の全余錐。使われ方：単一表示の結論。 -/
lemma smallFinitePosetDiagramCommaCocone_isColimit :
    IsColimitCone (smallDiagramCommaCocone κ D) :=
  smallDiagramCommaCocone_isColimit_of_evaluation_cofinal κ D
    (smallDiagramCommaEvaluation_finitePoset_isRightCofinal κ D)

/-- 概要：元の有限半順序全図式そのものに小さい単一 κ-filtered Yoneda 表示がある。
方針：同じ実表示 comma の filtered 性と各点密度。
規約：同じ D の厳密な頂点。使われ方：Ind の有限存在と安定性の次工程。 -/
lemma indFinitePoset_has_singleFilteredDiagramPresentation :
    HasSingleFilteredDiagramPresentation κ D :=
  hasSingleFilteredDiagramPresentation_of_evaluation_cofinal κ D
    (smallFinitePosetDiagramComma_isKappaFiltered κ D)
    (smallDiagramCommaEvaluation_finitePoset_isRightCofinal κ D)

end SerrePositivity.InfinityCategories.F2.Ind
