module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeTargetEvaluationFiltered
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeRestrictionCofinality

/-!
概要：下方 comma の filtered 性から、元の余錐図式の新しい極大点評価の共終性を得る。
方針：指定点下の実引き戻しの filtered 性と Quillen A を適用する。
規約：元の全評価写像を保持し、モデル圏仮定を追加しない。
使われ方：有限半順序形状の点追加で各頂点の標準密度を回収する。
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
include hL hLower
/-- 概要：下方の filtered 性から、元の極大点評価自身は right cofinal。
方針：元の点下の実 comma の弱可縮性。規約：同じ全評価。使われ方：各点の密度。 -/
lemma diagramCommaEvaluation_cone_apex_isRightCofinal :
    IsRightCofinal (diagramCommaEvaluation κ D (coneApex L)) := by
  apply isRightCofinal_of_weaklyContractible_lifted_point_under
  intro z
  have := indConeTargetEvaluationComma_isFiltered κ D hL hLower
    (isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le (Δ[0] : SSet.{u})) z
  exact isWeaklyContractible_of_isFilteredInfinity _
/-- 概要：同じ小さい表示添字の極大点評価自身も right cofinal。
方針：元の模型同型を合成。規約：同じ全評価。使われ方：単一 filtered 表示。 -/
lemma smallDiagramCommaEvaluation_cone_apex_isRightCofinal :
    IsRightCofinal (smallDiagramCommaEvaluation κ D (coneApex L)) :=
  (isRightCofinal_of_isIso (smallDiagramCommaIso κ D).hom).comp
    (diagramCommaEvaluation_cone_apex_isRightCofinal κ D hL hLower)
end SerrePositivity.InfinityCategories.F2.Ind
