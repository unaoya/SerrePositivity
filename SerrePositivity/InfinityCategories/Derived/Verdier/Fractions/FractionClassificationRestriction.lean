module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionKanCosliceClassification
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoComponent
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality

/-! # 指定した商上の分類同型を元の底へ制限すると、同じ元の分類同型を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 全写像空間の充満忠実性で選んだ分類同型は、元の指定した制限同型そのものへ写る。 -/
theorem fractionKanQuotientDiagram_classificationIso_pre :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map q.hom)).app
      SpaceInfinity)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom =
      (fractionKanQuotientDiagram_restrictionIso h x).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationIso q.hom x).hom := by
  exact (spaceLocalizationPre_fullyFaithful q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i)
    h.quotient).toHoFullyFaithful.map_preimage
      (X := HomotopyCategory.mk (functorVertex (fractionKanQuotientDiagram h x)))
      (Y := HomotopyCategory.mk (functorVertex (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))))) _

/-- 同じ分類同型の商像成分は、実制限同型で戻すと底上の元の分類同型の同じ成分。 -/
theorem fractionKanQuotientDiagram_classificationIso_component (y : B.obj _⦋0⦌) :
    ((fractionKanQuotientDiagram_restrictionIso h x).app (ULift.up y)).inv ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y)) =
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationIso q.hom x).hom
        (ULift.up y) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map q.hom
  let F := fractionKanQuotientDiagram h x
  let G := leftStraighteningInfinityDiagram
    (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
  let S := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram q.hom x
  let a : FunctorHom (k ≫ F) (k ≫ G) :=
    (hoFunctor.map ((pre k).app SpaceInfinity)).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom
  have he := congrArg (fun m : FunctorHom (k ≫ F) (k ≫ G) =>
    functorHomEvaluate m (ULift.up y)) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso_pre h x)
  change functorHomEvaluate a (ULift.up y) = functorHomEvaluate
    ((fractionKanQuotientDiagram_restrictionIso h x).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationIso q.hom x).hom) (ULift.up y) at he
  rw [functorHomEvaluate_comp (U := k ≫ F) (V := S) (W := k ≫ G)] at he
  have hp : functorHomEvaluate a (ULift.up y) =
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y)) :=
    functorHomEvaluate_precomp (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom k
      (ULift.up y)
  rw [hp] at he
  simp only [← _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate] at he
  have hc := congrArg (fun m =>
    ((fractionKanQuotientDiagram_restrictionIso h x).app (ULift.up y)).inv ≫ m) he
  have hn := hc
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hn
  simpa only [_root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate] using hn

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanQuotientDiagram_classificationIso_component := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso_component

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanQuotientDiagram_classificationIso_pre := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso_pre
