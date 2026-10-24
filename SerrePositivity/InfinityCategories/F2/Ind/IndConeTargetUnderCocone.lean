module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeCommaCoconeComparison
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedSliceRelative
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointEvaluationNaturality

/-!
概要：元の余錐図式族と極大点評価への指定変換を、同じ実 under comma で延長する。
方針：初期全円柱を保つ相対拡張と、旧族上で不変な指定比較を組み合わせる。
規約：元の q と指定変換を保持し、追加の充填入力を課さない。
使われ方：余錐形状の新しい極大点評価の共終性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：指定下方余錐から、元の極大点評価下の任意の試験族に実余錐を作る。
方針：指定比較を旧族で厳密に相殺。規約：元の q と指定値。使われ方：共終性の相対条件。 -/
lemma nonempty_indConeTargetUnder_cocone_of_lower_cocone
    (κ : Cardinal.{u}) [Fact κ.IsRegular] {L C A B : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L) (hB : IsKappaSmall κ B)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ leftKanShape (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L))))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u}))))
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (ht : q ≫ diagramCommaEvaluation κ D (coneApex L) = t ≫ sliceUnderProjection z) :
    Nonempty (JoinCocone
      (relativeCommaFamily (diagramCommaEvaluation κ D (coneApex L)) z t q ht)) := by
  obtain ⟨V⟩ := indConeExtendedSliceData_nonempty κ D q G hA hL
  let i := joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) (Δ[0] : SSet.{u + 1})
  let d := (indConeEndpointEvaluationIso V).precomp i
  have hq : i ≫ (indConeExtendedCommaFamily V ≫ diagramCommaEvaluation κ D (coneApex L)) =
      q ≫ diagramCommaEvaluation κ D (coneApex L) := by
    rw [← Category.assoc, indConeExtendedCommaFamily_old]
  let d' := F2.functorIsoOfEq d rfl (hq.trans ht)
  let s := pathCorrectedFunctorSquare (sliceUnderProjection z)
    (leftFibration_equivalenceLifting _) t
    (i ≫ (indConeEndpointRawFace V ≫ (indConeEndpointCommaIso κ D).hom)) d'
  obtain ⟨V', c, hInitial, hc⟩ := exists_indConeExtendedSliceData_relative κ D V hA hL hB
    z s.map s.comm.symm
  have hs : HEq (s.exactComponentIso.postcomp (sliceUnderProjection z)) d' :=
    (F2.functorIsoOfEq_heq _ s.comm rfl).symm.trans
      (heq_of_eq s.exactComponentIso_postcomp_normalized)
  have hCompare : HEq (s.exactComponentIso.postcomp (sliceUnderProjection z))
      ((indConeEndpointEvaluationIso V').precomp i) :=
    hs.trans ((F2.functorIsoOfEq_heq d rfl (hq.trans ht)).trans
      (indConeEndpointEvaluationIso_old_heq V V' hInitial.symm))
  exact nonempty_relativeCommaFamily_cocone_of_comparison
    (diagramCommaEvaluation κ D (coneApex L)) z q t ht
    (indConeExtendedCommaFamily V') (indConeExtendedCommaFamily_old V')
    (indConeEndpointRawFace V' ≫ (indConeEndpointCommaIso κ D).hom)
    (indConeEndpointEvaluationIso V') s.map c hc.symm s.exactComponentIso hCompare
end SerrePositivity.InfinityCategories.F2.Ind
