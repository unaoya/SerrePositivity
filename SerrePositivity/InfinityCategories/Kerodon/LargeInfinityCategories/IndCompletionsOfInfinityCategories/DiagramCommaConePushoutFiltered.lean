module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaConePushoutExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalityOfCoconeLifts
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.SmallDiagramComma

/-!
概要：極大点の局所余錐を貼る形状 pushout で、既存部分の filtered 性と共終性を伝える。
方針：元の指定余錐の厳密な持ち上げで、全体の filtered 性と制限の共終性を得る。
規約：元の添字・制限写像・全図式を保持する。
使われ方：有限半順序集合の極大点除去に関する帰納。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {L K₁ K C : SSet.{u}} [Quasicategory C]
  {i : L ⟶ K₁} {r : K₁ ⟶ K} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L (Δ[0] : SSet.{u}) ⟶ K}
  (h : IsPushout i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})) r s)
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
  (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L)
  (hOld : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramComma κ ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D)))
include h hL hOld
/-- 概要：既存部分の filtered 性から、元の全図式の任意の小さい族へ実余錐。
方針：既存部分の指定余錐を持ち上げる。規約：元の q。使われ方：全体の filtered 性。 -/
lemma nonempty_diagramComma_cone_pushout_cocone {A : SSet.{u}} (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) := by
  letI := hOld
  obtain ⟨c₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nonempty_cocone_liftedShape_of_equivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaIso κ
      ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D))) hA
    (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D r)
  obtain ⟨c, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_diagramComma_cocone_cone_pushout κ h D hA hL q c₁
  exact ⟨c⟩
/-- 概要：元の全図式の同じ小さい実 comma は κ-filtered。
方針：持ち上げた元の全試験族の余錐を降ろす。規約：元の添字。使われ方：点追加の帰納。 -/
lemma smallDiagramComma_cone_pushout_isKappaFiltered :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramComma κ D) := by
  constructor
  intro A hA f
  let q := (SSet.uliftFunctor.{u + 1, u}).map f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaIso κ D).hom
  obtain ⟨c⟩ := nonempty_diagramComma_cone_pushout_cocone κ h D hL hOld hA q
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map f) := by
    simpa only [q, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaIso κ D).inv c
  obtain ⟨d, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift_surjective.{u, u + 1} f hc
  exact ⟨d⟩
/-- 概要：元の全 comma から既存部分への同じ形状制限は right cofinal。
方針：元の指定像余錐を厳密に持ち上げる。規約：元の全制限。使われ方：旧頂点の密度。 -/
lemma diagramCommaRestriction_cone_pushout_isRightCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D r) := by
  letI := hOld
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_of_cocone_lifts (κ := κ) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D r) ?_ ?_
  · intro B hB p
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nonempty_cocone_liftedShape_of_equivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaIso κ
        ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D))) hB p
  · intro B hB p G
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_diagramComma_cocone_cone_pushout κ h D hB hL p G
/-- 概要：既存部分の各指定点の共終性は同じ全図式の元の評価へ伝わる。
方針：元の制限と評価の厳密な合成則。規約：元の評価写像。使われ方：旧頂点の帰納。 -/
lemma diagramCommaEvaluation_cone_pushout_old_isRightCofinal (k : K₁ _⦋0⦌)
    (hk : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation κ
      ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation κ D (r.app (Opposite.op ⦋0⦌) k)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction_evaluate κ D r k]
  exact (diagramCommaRestriction_cone_pushout_isRightCofinal κ h D hL hOld).comp hk
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
