module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaPushoutRightLift
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaConePushoutFiltered
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeTargetEvaluationCofinality

/-!
概要：共有下方部分への指定余錐持ち上げから、点追加の局所余錐部分と新頂点の共終性。
方針：右指定余錐を保つ pushout 貼り合わせと、局所余錐の極大点評価を合成する。
規約：必要な共有部分の持ち上げ条件を明示し、元の全評価写像を保持する。
使われ方：有限半順序形状の下方閉部分を固定する帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {L K₁ K C : SSet.{u}} [Quasicategory C]
  {i : L ⟶ K₁} {r : K₁ ⟶ K} {s : join L (Δ[0] : SSet.{u}) ⟶ K}
  (h : IsPushout i (joinInl L (Δ[0] : SSet.{u})) r s)
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
  (hL : IsKappaSmall κ L)
  (hLower : IsKappaFiltered κ (smallDiagramComma κ
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫
      (SSet.uliftFunctor.{u + 1, u}).map s ≫ D)))
  (hLift : ∀ {A : SSet.{u}}, IsKappaSmall κ A →
    ∀ q₁ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      diagramComma κ ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D),
    ∀ G : JoinCocone (q₁ ≫ diagramCommaRestriction κ
      ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) i),
    ∃ c₁ : JoinCocone q₁, mapJoinCocone (diagramCommaRestriction κ
      ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) i) c₁ = G)
include h hL hLower hLift
/-- 概要：元の局所余錐部分への制限は right cofinal。
方針：元の右指定余錐の厳密な持ち上げ。規約：元の制限。使われ方：新頂点の評価。 -/
lemma diagramCommaRestriction_cone_pushout_right_isRightCofinal :
    IsRightCofinal (diagramCommaRestriction κ D s) := by
  apply isRightCofinal_of_cocone_lifts (κ := κ) (diagramCommaRestriction κ D s) ?_ ?_
  · intro A hA q
    exact nonempty_indConeDiagramComma_cocone κ
      ((SSet.uliftFunctor.{u + 1, u}).map s ≫ D) hL hLower hA q
  · intro A hA q G
    exact exists_diagramComma_cocone_pushout_fix_right κ h D (hLift hA) q G
/-- 概要：元の点追加で同じ新頂点評価そのものは right cofinal。
方針：元の局所余錐部分への制限と極大点評価を合成する。
規約：同じ元の評価写像。使われ方：点追加の各点密度。 -/
lemma diagramCommaEvaluation_cone_pushout_apex_isRightCofinal :
    IsRightCofinal (diagramCommaEvaluation κ D (s.app (Opposite.op ⦋0⦌) (coneApex L))) := by
  rw [← diagramCommaRestriction_evaluate κ D s (coneApex L)]
  exact (diagramCommaRestriction_cone_pushout_right_isRightCofinal κ h D hL hLower hLift).comp
    (diagramCommaEvaluation_cone_apex_isRightCofinal κ
      ((SSet.uliftFunctor.{u + 1, u}).map s ≫ D) hL hLower)
end SerrePositivity.InfinityCategories.F2.Ind
