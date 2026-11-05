module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakQuotientMappingComparison
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoComponent
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality

/-! # 元の商・初頂点の制限式を、指定済みの同じ制限同型の実成分で正規化する -/

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

/-- 同じ商上の比較の成分を元の実制限同型で戻すと、底上の比較の同じ成分を回収。 -/
theorem weakQuotientMappingComparison_component_restriction (y : B.obj _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_restrictionIso h x).app (ULift.up y)).inv ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y)) ≫
      ((fractionKanQuotientDiagram_restrictionIso h x).app (ULift.up y)).hom =
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison h x) (ULift.up y) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map q.hom
  let S := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanSpaceDiagram i x
  let T := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram q.hom x
  let F := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x
  let G := fractionKanQuotientDiagram h x
  let a : FunctorHom (k ≫ F) (k ≫ G) :=
    (hoFunctor.map ((pre k).app SpaceInfinity)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison h x)
  have he := congrArg (fun m : FunctorHom S T => functorHomEvaluate m (ULift.up y))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison_pre_normalized h x)
  change functorHomEvaluate ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_restrictionIso h x).inv ≫
    a ≫ (fractionKanQuotientDiagram_restrictionIso h x).hom) (ULift.up y) = _ at he
  rw [functorHomEvaluate_comp (U := S) (V := k ≫ F) (W := T),
    functorHomEvaluate_comp (U := k ≫ F) (V := k ≫ G) (W := T)] at he
  have hp : functorHomEvaluate a (ULift.up y) =
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y)) :=
    functorHomEvaluate_precomp (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison h x) k (ULift.up y)
  rw [hp] at he
  simpa only [_root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_inv_evaluate] using he

/-- 同じ初頂点降下の比較成分を戻すと、元の strict Kan 比較辺の同じ頂点成分を回収。 -/
theorem weakSpanSpaceMappingComparison_component_restriction
    (c : TransportSimplexCategory B.obj) :
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanSpaceDiagram_restrictionIso i x).app (ULift.up (nerveVertex c))).inv ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison h x)
        (ULift.up ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
          (nerveVertex c))) ≫
      ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso q.hom x).app
        (ULift.up (nerveVertex c))).hom =
      functorHomEvaluate (Truncated.HomotopyCategory.homMk
        (weakSpanKanMappingComparisonEdge h x).toTruncated) (ULift.up (nerveVertex c)) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj)
  let F := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanSpaceDiagram i x
  let G := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram q.hom x
  let S := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanCoherentDiagram i x
  let T := kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x)
  let a : FunctorHom (k ≫ F) (k ≫ G) :=
    (hoFunctor.map ((pre k).app SpaceInfinity)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison h x)
  let z := ULift.up.{u + 1} (nerveVertex c)
  have he := congrArg (fun m : FunctorHom (k ≫ F) (k ≫ G) => functorHomEvaluate m z)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison_pre h x)
  change functorHomEvaluate a z = functorHomEvaluate
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanSpaceDiagram_restrictionIso i x).hom ≫
      Truncated.HomotopyCategory.homMk (weakSpanKanMappingComparisonEdge h x).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso q.hom x).inv) z at he
  rw [functorHomEvaluate_comp (U := k ≫ F) (V := S) (W := k ≫ G),
    functorHomEvaluate_comp (U := S) (V := T) (W := k ≫ G)] at he
  have hp : functorHomEvaluate a z = functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison h x)
      (ULift.up ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
        (nerveVertex c))) := functorHomEvaluate_precomp (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison h x) k z
  rw [hp] at he
  simp only [← _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate, ← _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_inv_evaluate] at he
  have hc := congrArg (fun m =>
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanSpaceDiagram_restrictionIso i x).app z).inv ≫ m ≫
      ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso q.hom x).app z).hom) he
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hc

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientMappingComparison_component_restriction := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison_component_restriction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSpaceMappingComparison_component_restriction := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison_component_restriction
