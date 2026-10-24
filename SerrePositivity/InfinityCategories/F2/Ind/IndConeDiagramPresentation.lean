module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeTargetEvaluationCofinality
public import SerrePositivity.InfinityCategories.F2.Ind.ConeVertexCases
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramFilteredPresentation

/-!
概要：下方の filtered 性と各点密度から、同じ余錐図式の単一 filtered 表示を得る。
方針：元の旧頂点評価と新しい極大点評価の共終性を同じ標準全余錐へ渡す。
規約：下方条件を明示し、元の全図式 D 自身を頂点とする。
使われ方：有限半順序形状の局所点追加と単一表示の帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {L C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
  (hL : IsKappaSmall κ L)
  (hLower : IsKappaFiltered κ (smallDiagramComma κ
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D)))
  (hEval : ∀ l : L _⦋0⦌, IsRightCofinal (diagramCommaEvaluation κ
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D) l))
include hL hLower hEval
/-- 概要：下方の各点共終性は、同じ全余錐図式の全頂点で共終性を与える。
方針：元の二種類の頂点を列挙。規約：全評価写像。使われ方：標準全余錐の密度。 -/
lemma diagramCommaEvaluation_cone_isRightCofinal
    (k : (join L (Δ[0] : SSet.{u})) _⦋0⦌) :
    IsRightCofinal (diagramCommaEvaluation κ D k) := by
  rcases coneVertex_cases k with ⟨l, rfl⟩ | rfl
  · exact diagramCommaEvaluation_cone_inl_isRightCofinal κ D hL hLower l (hEval l)
  · exact diagramCommaEvaluation_cone_apex_isRightCofinal κ D hL hLower
/-- 概要：同じ小さい元の comma の全頂点評価は共終的。
方針：元の模型同型で前合成。規約：全評価写像。使われ方：単一 filtered 表示。 -/
lemma smallDiagramCommaEvaluation_cone_isRightCofinal
    (k : (join L (Δ[0] : SSet.{u})) _⦋0⦌) :
    IsRightCofinal (smallDiagramCommaEvaluation κ D k) :=
  (isRightCofinal_of_isIso (smallDiagramCommaIso κ D).hom).comp
    (diagramCommaEvaluation_cone_isRightCofinal κ D hL hLower hEval k)
/-- 概要：下方の filtered 性と各点密度から元の全余錐図式の単一表示。
方針：同じ標準全余錐の余極限性。規約：頂点は元の D。使われ方：点追加の表示帰納。 -/
lemma indCone_has_singleFilteredDiagramPresentation : HasSingleFilteredDiagramPresentation κ D :=
  hasSingleFilteredDiagramPresentation_of_evaluation_cofinal κ D
    (smallConeDiagramComma_isKappaFiltered_of_lower κ D hL hLower)
    (smallDiagramCommaEvaluation_cone_isRightCofinal κ D hL hLower hEval)
end SerrePositivity.InfinityCategories.F2.Ind
