module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaConePushoutExtension
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalityOfCoconeLifts
public import SerrePositivity.InfinityCategories.F2.Ind.SmallDiagramComma

/-!
概要：極大点の局所余錐を貼る形状 pushout で、既存部分の filtered 性と共終性を伝える。
方針：元の指定余錐の厳密な持ち上げで、全体の filtered 性と制限の共終性を得る。
規約：元の添字・制限写像・全図式を保持する。
使われ方：有限半順序集合の極大点除去に関する帰納。
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
  (hOld : IsKappaFiltered κ
    (smallDiagramComma κ ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D)))
include h hL hOld
/-- 概要：既存部分の filtered 性から、元の全図式の任意の小さい族へ実余錐。
方針：既存部分の指定余錐を持ち上げる。規約：元の q。使われ方：全体の filtered 性。 -/
lemma nonempty_diagramComma_cone_pushout_cocone {A : SSet.{u}} (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D) :
    Nonempty (JoinCocone q) := by
  letI := hOld
  obtain ⟨c₁⟩ := nonempty_cocone_liftedShape_of_equivalence
    (qCatEquivalenceOfIso (smallDiagramCommaIso κ
      ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D))) hA
    (q ≫ diagramCommaRestriction κ D r)
  obtain ⟨c, _⟩ := exists_diagramComma_cocone_cone_pushout κ h D hA hL q c₁
  exact ⟨c⟩
/-- 概要：元の全図式の同じ小さい実 comma は κ-filtered。
方針：持ち上げた元の全試験族の余錐を降ろす。規約：元の添字。使われ方：点追加の帰納。 -/
lemma smallDiagramComma_cone_pushout_isKappaFiltered :
    IsKappaFiltered κ (smallDiagramComma κ D) := by
  constructor
  intro A hA f
  let q := (SSet.uliftFunctor.{u + 1, u}).map f ≫ (smallDiagramCommaIso κ D).hom
  obtain ⟨c⟩ := nonempty_diagramComma_cone_pushout_cocone κ h D hL hOld hA q
  have hc : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map f) := by
    simpa only [q, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      mapJoinCocone (smallDiagramCommaIso κ D).inv c
  obtain ⟨d, _⟩ := JoinCocone.ulift_surjective.{u, u + 1} f hc
  exact ⟨d⟩
/-- 概要：元の全 comma から既存部分への同じ形状制限は right cofinal。
方針：元の指定像余錐を厳密に持ち上げる。規約：元の全制限。使われ方：旧頂点の密度。 -/
lemma diagramCommaRestriction_cone_pushout_isRightCofinal :
    IsRightCofinal (diagramCommaRestriction κ D r) := by
  letI := hOld
  apply isRightCofinal_of_cocone_lifts (κ := κ) (diagramCommaRestriction κ D r) ?_ ?_
  · intro B hB p
    exact nonempty_cocone_liftedShape_of_equivalence
      (qCatEquivalenceOfIso (smallDiagramCommaIso κ
        ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D))) hB p
  · intro B hB p G
    exact exists_diagramComma_cocone_cone_pushout κ h D hB hL p G
/-- 概要：既存部分の各指定点の共終性は同じ全図式の元の評価へ伝わる。
方針：元の制限と評価の厳密な合成則。規約：元の評価写像。使われ方：旧頂点の帰納。 -/
lemma diagramCommaEvaluation_cone_pushout_old_isRightCofinal (k : K₁ _⦋0⦌)
    (hk : IsRightCofinal (diagramCommaEvaluation κ
      ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) k)) :
    IsRightCofinal (diagramCommaEvaluation κ D (r.app (Opposite.op ⦋0⦌) k)) := by
  rw [← diagramCommaRestriction_evaluate κ D r k]
  exact (diagramCommaRestriction_cone_pushout_isRightCofinal κ h D hL hOld).comp hk
end SerrePositivity.InfinityCategories.F2.Ind
