module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionClassificationRestriction

/-! # 指定した分類同型を初頂点へ制限し、同じ実 section 比較を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 初頂点局所化で降下した同じ分類同型の像は、指定された元の制限同型そのもの。 -/
theorem fractionKanSpaceDiagram_classificationIso_pre {X Q : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] (F : X ⟶ Q) (x : X _⦋0⦌) :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map
      (transportSimplexFirstVertexMap X))).app SpaceInfinity)).toFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationIso F x).hom =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationRestrictionIso F x).hom := by
  exact (localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} X)
    SpaceInfinity.{u}).toHoFullyFaithful.map_preimage
      (X := HomotopyCategory.mk (functorVertex (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram F x)))
      (Y := HomotopyCategory.mk (functorVertex
        ((SSet.uliftFunctor.{u + 1, u}).map F ≫ leftStraighteningInfinityDiagram
          (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))))) _

/-- 同じ分類同型の初頂点成分は、指定された全 section 比較の同じ成分。 -/
theorem fractionKanSpaceDiagram_classificationIso_component {X Q : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] (F : X ⟶ Q) (x : X _⦋0⦌)
    (c : TransportSimplexCategory X) :
    functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationIso F x).hom
      (ULift.up ((transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌) (nerveVertex c))) =
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationRestrictionIso F x).hom
        (ULift.up (nerveVertex c)) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap X)
  let S := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram F x
  let T := (SSet.uliftFunctor.{u + 1, u}).map F ≫ leftStraighteningInfinityDiagram
    (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
  have he := congrArg (fun m : FunctorHom (k ≫ S) (k ≫ T) =>
    functorHomEvaluate m (ULift.up (nerveVertex c)))
    (fractionKanSpaceDiagram_classificationIso_pre F x)
  exact (functorHomEvaluate_precomp (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationIso F x).hom
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap X))
    (ULift.up (nerveVertex c))).symm.trans he

end SerrePositivity.KST.Fibration
