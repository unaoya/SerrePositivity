module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeTargetUnderCocone
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeDiagramFiltered
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeFilteredCriterion

/-!
概要：下方 comma が κ-filtered なら、元の余錐図式の極大点評価下の実 comma は filtered。
方針：元の指定変換下の任意の小さい全族に実余錐を作る。
規約：元の評価写像と指定下側変換を保持する。
使われ方：新しい極大点評価の Quillen A。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {L C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
  (hL : IsKappaSmall κ L)
  (hLower : IsKappaFiltered κ (smallDiagramComma κ
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D)))
include hL hLower
/-- 概要：下方の filtered 性から、元の極大点評価下の任意の指定族に実余錐。
方針：元の下方余錐を選び相対拡張する。規約：元の q と指定 t。使われ方：共終性。 -/
lemma nonempty_indConeTargetUnder_cocone {A B : SSet.{u}}
    (hA : IsKappaSmall κ A) (hB : IsKappaSmall κ B)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ leftKanShape (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L))))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (ht : q ≫ diagramCommaEvaluation κ D (coneApex L) = t ≫ sliceUnderProjection z) :
    Nonempty (JoinCocone
      (relativeCommaFamily (diagramCommaEvaluation κ D (coneApex L)) z t q ht)) := by
  letI := hLower
  obtain ⟨G⟩ := nonempty_cocone_liftedShape_of_equivalence
    (qCatEquivalenceOfIso (smallDiagramCommaIso κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D))) hA
    (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))
  exact nonempty_indConeTargetUnder_cocone_of_lower_cocone κ D hA hL hB z q G t ht
/-- 概要：同じ元の極大点評価の実引き戻しの小さい試験族は実余錐を持つ。
方針：二射影を元の相対族へ束ね直す。規約：元の引き戻し。使われ方：filtered 判定。 -/
lemma nonempty_indConeTargetEvaluationComma_cocone {A B : SSet.{u}}
    (hA : IsKappaSmall κ A) (hB : IsKappaSmall κ B)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ leftKanShape (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L))))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      pullback (sliceUnderProjection z) (diagramCommaEvaluation κ D (coneApex L))) :
    Nonempty (JoinCocone q) := by
  let e := diagramCommaEvaluation κ D (coneApex L)
  let p := sliceUnderProjection z
  have h : (q ≫ pullback.snd p e) ≫ e = (q ≫ pullback.fst p e) ≫ p := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hc := nonempty_indConeTargetUnder_cocone κ D hL hLower hA hB z
    (q ≫ pullback.snd p e) (q ≫ pullback.fst p e) h
  have hq : relativeCommaFamily e z (q ≫ pullback.fst p e) (q ≫ pullback.snd p e) h = q := by
    apply pullback.hom_ext <;> simp only [relativeCommaFamily, pullback.lift_fst,
      pullback.lift_snd] <;> rfl
  exact hq ▸ hc
/-- 概要：同じ指定下側図式の下の元の極大点評価 comma は filtered。
方針：任意の小さい試験族の実余錐。規約：元の評価。使われ方：共終性。 -/
lemma indConeTargetEvaluationComma_isFiltered {B : SSet.{u}} (hB : IsKappaSmall κ B)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ leftKanShape (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L)))) :
    IsFilteredInfinity
      (pullback (sliceUnderProjection z) (diagramCommaEvaluation κ D (coneApex L))) := by
  apply isFilteredInfinity_of_liftedShape_cocones (Fact.out : κ.IsRegular)
  intro A hA q
  exact nonempty_indConeTargetEvaluationComma_cocone κ D hL hLower hA hB z q
end SerrePositivity.InfinityCategories.F2.Ind
