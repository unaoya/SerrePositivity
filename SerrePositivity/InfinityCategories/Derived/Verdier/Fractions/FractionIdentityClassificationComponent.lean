module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionNativeClassificationComponent
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakNativeClassificationPoint

/-! # 商上の指定分類成分を、元の同じ零添字の section 分類成分へ戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration

private theorem component_reindex_target {D X : SSet.{u}} {F G : D ⟶ X}
    (α : FunctorHom F G) {p q : D _⦋0⦌} (hp : p = q)
    {S : hoFunctor.obj X} (s : HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) p) ≅ S) :
    (eqToIso (congrArg HomotopyCategory.mk
      (congrArg (F.app (Opposite.op ⦋0⦌)) hp.symm)) ≪≫ s).inv ≫
      functorHomEvaluate α q = s.inv ≫ functorHomEvaluate α p ≫
        eqToHom (congrArg HomotopyCategory.mk
          (congrArg (G.app (Opposite.op ⦋0⦌)) hp)) := by
  cases hp
  simp only [eqToIso_refl, Iso.refl_trans, eqToHom_refl, Category.comp_id]

variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 同じ商分類の成分を元の値同型で戻すと、section 比較から作った同じ native 成分になる。 -/
theorem fractionKanQuotientDiagram_classificationIso_native_component
    (c : TransportSimplexCategory B.obj) :
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_initialVertexIso h x c).inv ≫
      functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌)
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))) =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso q.hom x c).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_initialVertexIso, Iso.trans_inv, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso_component]
  exact _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSpaceDiagram_classificationIso_native_component q.hom x c

/-- 指定分類成分の零添字値。初頂点表示だけを元の商像へ揃えた同じ実同型。 -/
def fractionIdentityNativeClassificationIso :
    VertexIso (spaceInfinityVertex ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).obj
      (transportSimplexIndex (n := ⦋0⦌) x)))
      ((leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))).app
          (Opposite.op ⦋0⦌) (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x))) :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso q.hom x (transportSimplexIndex (n := ⦋0⦌) x) ≪≫
    eqToIso (congrArg HomotopyCategory.mk (congrArg
      ((leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))).app
          (Opposite.op ⦋0⦌))
      (congrArg (fun y => ULift.up.{u + 1} (q.hom.app (Opposite.op ⦋0⦌) y))
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x))))

/-- 元の商で指定した分類射は、同じ section・表現・底変換を保持した零添字成分の射そのもの。 -/
theorem fractionIdentityNativeClassificationHom_eq :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationHom h x =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationIso (q := q) x).hom := by
  have hp : ULift.up.{u + 1} (q.hom.app (Opposite.op ⦋0⦌)
      ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)))) =
      ULift.up (q.hom.app (Opposite.op ⦋0⦌) x) :=
    congrArg (fun y => ULift.up (q.hom.app (Opposite.op ⦋0⦌) y))
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x)
  have he := component_reindex_target (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso h x).hom hp
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_initialVertexIso h x (transportSimplexIndex (n := ⦋0⦌) x))
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso_native_component] at he
  exact he

/-- 合成の実恒等点は、降下を外した同じ section 分類成分による native 比較像そのもの。 -/
theorem weakQuotientCosliceCompositePoint_section_image_hom :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageHom h x ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationIso (q := q) x).hom =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram
          (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint h x)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationHom_eq h x]
  exact _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_native_image_hom h x

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionIdentityNativeClassificationHom_eq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationHom_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionIdentityNativeClassificationIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanQuotientDiagram_classificationIso_native_component := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_classificationIso_native_component

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientCosliceCompositePoint_section_image_hom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientCosliceCompositePoint_section_image_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionIdentityNativeClassificationIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionIdentityNativeClassificationIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionIdentityNativeClassificationIso._proof_2
