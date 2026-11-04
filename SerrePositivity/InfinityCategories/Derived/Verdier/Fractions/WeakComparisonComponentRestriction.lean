module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakQuotientMappingComparison
public import SerrePositivity.KST.Fibration.FunctorIsoComponent
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality

/-! # 元の商・初頂点の制限式を、指定済みの同じ制限同型の実成分で正規化する -/

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

/-- 同じ商上の比較の成分を元の実制限同型で戻すと、底上の比較の同じ成分を回収。 -/
theorem weakQuotientMappingComparison_component_restriction (y : B.obj _⦋0⦌) :
    ((weakSpanKanQuotientDiagram_restrictionIso h x).app (ULift.up y)).inv ≫
      functorHomEvaluate (weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y)) ≫
      ((fractionKanQuotientDiagram_restrictionIso h x).app (ULift.up y)).hom =
      functorHomEvaluate (weakSpanSpaceMappingComparison h x) (ULift.up y) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map q.hom
  let S := weakSpanKanSpaceDiagram i x
  let T := fractionKanSpaceDiagram q.hom x
  let F := weakSpanKanQuotientDiagram h x
  let G := fractionKanQuotientDiagram h x
  let a : FunctorHom (k ≫ F) (k ≫ G) :=
    (hoFunctor.map ((pre k).app SpaceInfinity)).toFunctor.map (weakQuotientMappingComparison h x)
  have he := congrArg (fun m : FunctorHom S T => functorHomEvaluate m (ULift.up y))
    (weakQuotientMappingComparison_pre_normalized h x)
  change functorHomEvaluate ((weakSpanKanQuotientDiagram_restrictionIso h x).inv ≫
    a ≫ (fractionKanQuotientDiagram_restrictionIso h x).hom) (ULift.up y) = _ at he
  rw [functorHomEvaluate_comp (U := S) (V := k ≫ F) (W := T),
    functorHomEvaluate_comp (U := k ≫ F) (V := k ≫ G) (W := T)] at he
  have hp : functorHomEvaluate a (ULift.up y) =
      functorHomEvaluate (weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y)) :=
    functorHomEvaluate_precomp (weakQuotientMappingComparison h x) k (ULift.up y)
  rw [hp] at he
  simpa only [functorIso_app_hom_evaluate, functorIso_app_inv_evaluate] using he

/-- 同じ初頂点降下の比較成分を戻すと、元の strict Kan 比較辺の同じ頂点成分を回収。 -/
theorem weakSpanSpaceMappingComparison_component_restriction
    (c : TransportSimplexCategory B.obj) :
    ((weakSpanKanSpaceDiagram_restrictionIso i x).app (ULift.up (nerveVertex c))).inv ≫
      functorHomEvaluate (weakSpanSpaceMappingComparison h x)
        (ULift.up ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
          (nerveVertex c))) ≫
      ((fractionKanSpaceDiagram_restrictionIso q.hom x).app
        (ULift.up (nerveVertex c))).hom =
      functorHomEvaluate (Truncated.HomotopyCategory.homMk
        (weakSpanKanMappingComparisonEdge h x).toTruncated) (ULift.up (nerveVertex c)) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj)
  let F := weakSpanKanSpaceDiagram i x
  let G := fractionKanSpaceDiagram q.hom x
  let S := weakSpanKanCoherentDiagram i x
  let T := kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram q.hom x)
  let a : FunctorHom (k ≫ F) (k ≫ G) :=
    (hoFunctor.map ((pre k).app SpaceInfinity)).toFunctor.map (weakSpanSpaceMappingComparison h x)
  let z := ULift.up.{u + 1} (nerveVertex c)
  have he := congrArg (fun m : FunctorHom (k ≫ F) (k ≫ G) => functorHomEvaluate m z)
    (weakSpanSpaceMappingComparison_pre h x)
  change functorHomEvaluate a z = functorHomEvaluate
    ((weakSpanKanSpaceDiagram_restrictionIso i x).hom ≫
      Truncated.HomotopyCategory.homMk (weakSpanKanMappingComparisonEdge h x).toTruncated ≫
      (fractionKanSpaceDiagram_restrictionIso q.hom x).inv) z at he
  rw [functorHomEvaluate_comp (U := k ≫ F) (V := S) (W := k ≫ G),
    functorHomEvaluate_comp (U := S) (V := T) (W := k ≫ G)] at he
  have hp : functorHomEvaluate a z = functorHomEvaluate (weakSpanSpaceMappingComparison h x)
      (ULift.up ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
        (nerveVertex c))) := functorHomEvaluate_precomp (weakSpanSpaceMappingComparison h x) k z
  rw [hp] at he
  simp only [← functorIso_app_hom_evaluate, ← functorIso_app_inv_evaluate] at he
  have hc := congrArg (fun m =>
    ((weakSpanKanSpaceDiagram_restrictionIso i x).app z).inv ≫ m ≫
      ((fractionKanSpaceDiagram_restrictionIso q.hom x).app z).hom) he
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hc

end SerrePositivity.KST.Fibration
