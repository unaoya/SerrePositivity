module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionKanCosliceClassification
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoComponent
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality

/-! # 指定した商上の分類同型を元の底へ制限すると、同じ元の分類同型を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 全写像空間の充満忠実性で選んだ分類同型は、元の指定した制限同型そのものへ写る。 -/
theorem fractionKanQuotientDiagram_classificationIso_pre :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map q.hom)).app
      SpaceInfinity)).toFunctor.map (fractionKanQuotientDiagram_classificationIso h x).hom =
      (fractionKanQuotientDiagram_restrictionIso h x).hom ≫
        (fractionKanSpaceDiagram_classificationIso q.hom x).hom := by
  exact (spaceLocalizationPre_fullyFaithful q.hom (weakEquivalences i)
    h.quotient).toHoFullyFaithful.map_preimage
      (X := HomotopyCategory.mk (functorVertex (fractionKanQuotientDiagram h x)))
      (Y := HomotopyCategory.mk (functorVertex (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))))) _

/-- 同じ分類同型の商像成分は、実制限同型で戻すと底上の元の分類同型の同じ成分。 -/
theorem fractionKanQuotientDiagram_classificationIso_component (y : B.obj _⦋0⦌) :
    ((fractionKanQuotientDiagram_restrictionIso h x).app (ULift.up y)).inv ≫
      functorHomEvaluate (fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y)) =
      functorHomEvaluate (fractionKanSpaceDiagram_classificationIso q.hom x).hom
        (ULift.up y) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map q.hom
  let F := fractionKanQuotientDiagram h x
  let G := leftStraighteningInfinityDiagram
    (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
  let S := fractionKanSpaceDiagram q.hom x
  let a : FunctorHom (k ≫ F) (k ≫ G) :=
    (hoFunctor.map ((pre k).app SpaceInfinity)).toFunctor.map
      (fractionKanQuotientDiagram_classificationIso h x).hom
  have he := congrArg (fun m : FunctorHom (k ≫ F) (k ≫ G) =>
    functorHomEvaluate m (ULift.up y)) (fractionKanQuotientDiagram_classificationIso_pre h x)
  change functorHomEvaluate a (ULift.up y) = functorHomEvaluate
    ((fractionKanQuotientDiagram_restrictionIso h x).hom ≫
      (fractionKanSpaceDiagram_classificationIso q.hom x).hom) (ULift.up y) at he
  rw [functorHomEvaluate_comp (U := k ≫ F) (V := S) (W := k ≫ G)] at he
  have hp : functorHomEvaluate a (ULift.up y) =
      functorHomEvaluate (fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y)) :=
    functorHomEvaluate_precomp (fractionKanQuotientDiagram_classificationIso h x).hom k
      (ULift.up y)
  rw [hp] at he
  simp only [← functorIso_app_hom_evaluate] at he
  have hc := congrArg (fun m =>
    ((fractionKanQuotientDiagram_restrictionIso h x).app (ULift.up y)).inv ≫ m) he
  have hn := hc
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hn
  simpa only [functorIso_app_hom_evaluate] using hn

end SerrePositivity.KST.Fibration
