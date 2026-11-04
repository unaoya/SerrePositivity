module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionNativeClassificationComponent
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakNativeClassificationPoint

/-! # 商上の指定分類成分を、元の同じ零添字の section 分類成分へ戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

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

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 同じ商分類の成分を元の値同型で戻すと、section 比較から作った同じ native 成分になる。 -/
theorem fractionKanQuotientDiagram_classificationIso_native_component
    (c : TransportSimplexCategory B.obj) :
    (fractionKanQuotientDiagram_initialVertexIso h x c).inv ≫
      functorHomEvaluate (fractionKanQuotientDiagram_classificationIso h x).hom
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌)
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))) =
      (fractionKanSimplexClassificationValueIso q.hom x c).hom := by
  simp only [fractionKanQuotientDiagram_initialVertexIso, Iso.trans_inv, Category.assoc]
  rw [fractionKanQuotientDiagram_classificationIso_component]
  exact fractionKanSpaceDiagram_classificationIso_native_component q.hom x c

/-- 指定分類成分の零添字値。初頂点表示だけを元の商像へ揃えた同じ実同型。 -/
def fractionIdentityNativeClassificationIso :
    VertexIso (spaceInfinityVertex ((fractionSimplexKanMappingDiagram q.hom x).obj
      (transportSimplexIndex (n := ⦋0⦌) x)))
      ((leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))).app
          (Opposite.op ⦋0⦌) (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x))) :=
  fractionKanSimplexClassificationValueIso q.hom x (transportSimplexIndex (n := ⦋0⦌) x) ≪≫
    eqToIso (congrArg HomotopyCategory.mk (congrArg
      ((leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))).app
          (Opposite.op ⦋0⦌))
      (congrArg (fun y => ULift.up.{u + 1} (q.hom.app (Opposite.op ⦋0⦌) y))
        (transportSimplexFirstVertexMap_zeroIndex x))))

/-- 元の商で指定した分類射は、同じ section・表現・底変換を保持した零添字成分の射そのもの。 -/
theorem fractionIdentityNativeClassificationHom_eq :
    fractionIdentityNativeClassificationHom h x =
      (fractionIdentityNativeClassificationIso (q := q) x).hom := by
  have hp : ULift.up.{u + 1} (q.hom.app (Opposite.op ⦋0⦌)
      ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)))) =
      ULift.up (q.hom.app (Opposite.op ⦋0⦌) x) :=
    congrArg (fun y => ULift.up (q.hom.app (Opposite.op ⦋0⦌) y))
      (transportSimplexFirstVertexMap_zeroIndex x)
  have he := component_reindex_target (fractionKanQuotientDiagram_classificationIso h x).hom hp
    (fractionKanQuotientDiagram_initialVertexIso h x (transportSimplexIndex (n := ⦋0⦌) x))
  rw [← Category.assoc, fractionKanQuotientDiagram_classificationIso_native_component] at he
  exact he

/-- 合成の実恒等点は、降下を外した同じ section 分類成分による native 比較像そのもの。 -/
theorem weakQuotientCosliceCompositePoint_section_image_hom :
    weakIdentityNativeComparisonImageHom h x ≫
      (fractionIdentityNativeClassificationIso (q := q) x).hom =
      cosliceFiberPointHom (smallUnstraighteningPointedImage
        (leftStraighteningInfinityDiagram
          (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
        (q.hom.app (Opposite.op ⦋0⦌) x) (weakQuotientCosliceCompositePoint h x)) := by
  rw [← fractionIdentityNativeClassificationHom_eq h x]
  exact weakQuotientCosliceCompositePoint_native_image_hom h x

end SerrePositivity.KST.Fibration
