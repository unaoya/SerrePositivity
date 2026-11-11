module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakQuotientMappingComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoComponent
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 同じ商上の比較の成分を元の実制限同型で戻すと、底上の比較の同じ成分を回収。 -/
theorem weakQuotientMappingComparison_component_restriction (y : B.obj _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram_restrictionIso h x).app (ULift.up y)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y)) ≫
      ((fractionKanQuotientDiagram_restrictionIso h x).app (ULift.up y)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x) (ULift.up y) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map q.hom
  let S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanSpaceDiagram i x
  let T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram q.hom x
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x
  let G := fractionKanQuotientDiagram h x
  let a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (k ≫ F) (k ≫ G) :=
    (hoFunctor.map ((pre k).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x)
  have he := congrArg (fun m : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom S T => _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate m (ULift.up y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison_pre_normalized h x)
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram_restrictionIso h x).inv ≫
    a ≫ (fractionKanQuotientDiagram_restrictionIso h x).hom) (ULift.up y) = _ at he
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp (U := S) (V := k ≫ F) (W := T),
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp (U := k ≫ F) (V := k ≫ G) (W := T)] at he
  have hp : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate a (ULift.up y) =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y)) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x) k (ULift.up y)
  rw [hp] at he
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIso_app_hom_evaluate, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIso_app_inv_evaluate] using he

/-- 同じ初頂点降下の比較成分を戻すと、元の strict Kan 比較辺の同じ頂点成分を回収。 -/
theorem weakSpanSpaceMappingComparison_component_restriction
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B.obj) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanSpaceDiagram_restrictionIso i x).app (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x)
        (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso q.hom x).app
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).hom =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (Truncated.HomotopyCategory.homMk
        (weakSpanKanMappingComparisonEdge h x).toTruncated) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj)
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanSpaceDiagram i x
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram q.hom x
  let S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanCoherentDiagram i x
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x)
  let a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (k ≫ F) (k ≫ G) :=
    (hoFunctor.map ((pre k).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x)
  let z := ULift.up.{u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)
  have he := congrArg (fun m : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (k ≫ F) (k ≫ G) => _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate m z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison_pre h x)
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate a z = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanSpaceDiagram_restrictionIso i x).hom ≫
      Truncated.HomotopyCategory.homMk (weakSpanKanMappingComparisonEdge h x).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso q.hom x).inv) z at he
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp (U := k ≫ F) (V := S) (W := k ≫ G),
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp (U := S) (V := T) (W := k ≫ G)] at he
  have hp : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate a z = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x)
      (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x) k z
  rw [hp] at he
  simp only [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIso_app_hom_evaluate, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIso_app_inv_evaluate] at he
  have hc := congrArg (fun m =>
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanSpaceDiagram_restrictionIso i x).app z).inv ≫ m ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso q.hom x).app z).hom) he
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientMappingComparison_component_restriction := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison_component_restriction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSpaceMappingComparison_component_restriction := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison_component_restriction
