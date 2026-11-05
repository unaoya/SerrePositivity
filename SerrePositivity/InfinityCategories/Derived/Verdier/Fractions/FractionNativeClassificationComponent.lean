module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.KST.Fibration.FractionClassificationSimplexRestriction

/-! # 指定分類成分を元の strict Kan 値で読むと、同じ section 比較の実成分を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory X] [Quasicategory Q]
  (F : X ⟶ Q) (x : X _⦋0⦌) (c : TransportSimplexCategory X)

/-- 指定した native Kan 値から実分類図式の同じ初頂点値への元の同型。 -/
def fractionKanSimplexClassificationValueIso :
    VertexIso (spaceInfinityVertex ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram F x).obj c))
      ((leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))).app
          (Opposite.op ⦋0⦌) (ULift.up (F.app (Opposite.op ⦋0⦌)
            ((transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌) (nerveVertex c))))) :=
  (eqToIso (congrArg HomotopyCategory.mk
    (kanDiagramCoherentNerve_vertex (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram F x) c))).symm ≪≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationIso F x).app (ULift.up (nerveVertex c))

/-- 底上の同じ分類成分を、元の指定値同型で戻すと同じ native 分類成分になる。 -/
theorem fractionKanSpaceDiagram_classificationIso_native_component :
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_initialVertexIso F x c).inv ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationIso F x).hom
        (ULift.up ((transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌) (nerveVertex c))) =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso F x c).hom := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap X)
  let S := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram F x
  let T := kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram F x)
  let G := (SSet.uliftFunctor.{u + 1, u}).map F ≫ leftStraighteningInfinityDiagram
    (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
  let z := ULift.up.{u + 1} (nerveVertex c)
  have he := fractionKanSpaceDiagram_classificationIso_component F x c
  change functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationIso F x).hom
      (ULift.up ((transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌) (nerveVertex c))) =
    functorHomEvaluate ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso F x).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationIso F x).hom) z at he
  rw [functorHomEvaluate_comp (U := k ≫ S) (V := T) (W := k ≫ G)] at he
  simp only [← _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate] at he
  have hc := congrArg (fun m => (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_initialVertexIso F x c).inv ≫ m) he
  dsimp only [z] at hc
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_initialVertexIso, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id_assoc] at hc
  simpa only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_initialVertexIso,
    Iso.trans_inv, Category.assoc, Iso.trans_hom, Iso.symm_hom,
    _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate] using hc

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSimplexClassificationValueIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSpaceDiagram_classificationIso_native_component := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationIso_native_component

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSimplexClassificationValueIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSimplexClassificationValueIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSimplexClassificationValueIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanSimplexClassificationValueIso.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso.eq_1
