module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakNativeComponentRestriction
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakIdentityQuotientPoint

/-! # 元の恒等 span の商上の比較像を、同じ strict Kan 比較の零添字成分へ戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

private theorem component_reindex_normalize {D X : SSet.{u}} {F G : D ⟶ X}
    (α : FunctorHom F G) {p q : D _⦋0⦌} (hp : p = q)
    {S T : hoFunctor.obj X} (s : HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) p) ≅ S)
    (t : HomotopyCategory.mk (G.app (Opposite.op ⦋0⦌) p) ≅ T) :
    (eqToIso (congrArg HomotopyCategory.mk
      (congrArg (F.app (Opposite.op ⦋0⦌)) hp.symm)) ≪≫ s).inv ≫
      functorHomEvaluate α q ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (congrArg (G.app (Opposite.op ⦋0⦌)) hp.symm)) ≪≫ t).hom =
      s.inv ≫ functorHomEvaluate α p ≫ t.hom := by
  cases hp
  simp only [eqToIso_refl, Iso.refl_trans]

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 商の coslice 図式の x の商像における値を、同じ零添字の strict Kan 値へ戻す。 -/
def fractionIdentityQuotientValueIso :
    VertexIso ((fractionKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)))
      (spaceInfinityVertex ((fractionSimplexKanMappingDiagram q.hom x).obj
        (transportSimplexIndex (n := ⦋0⦌) x))) := by
  have he : ULift.up.{u + 1} (q.hom.app (Opposite.op ⦋0⦌) x) =
      ULift.up (q.hom.app (Opposite.op ⦋0⦌)
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
          (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)))) :=
    congrArg ULift.up (congrArg (q.hom.app (Opposite.op ⦋0⦌))
      (transportSimplexFirstVertexMap_zeroIndex x).symm)
  exact eqToIso (congrArg HomotopyCategory.mk
    (congrArg ((fractionKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)) he)) ≪≫
      fractionKanQuotientDiagram_initialVertexIso h x (transportSimplexIndex (n := ⦋0⦌) x)

/-- 同じ商上の比較の x 成分は、元の指定済み値同型で戻すと同じ strict Kan 比較の零添字辺。 -/
theorem weakQuotientMappingComparison_identity_native :
    (weakIdentityQuotientValueIso h x).inv ≫
      functorHomEvaluate (weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
      (fractionIdentityQuotientValueIso h x).hom =
      Truncated.HomotopyCategory.homMk
        (weakSpanKanComparisonValueEdge h x (transportSimplexIndex (n := ⦋0⦌) x)).toTruncated := by
  have he : ULift.up.{u + 1} (q.hom.app (Opposite.op ⦋0⦌)
      ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)))) =
      ULift.up (q.hom.app (Opposite.op ⦋0⦌) x) :=
    congrArg ULift.up (congrArg (q.hom.app (Opposite.op ⦋0⦌))
      (transportSimplexFirstVertexMap_zeroIndex x))
  have hc := component_reindex_normalize (weakQuotientMappingComparison h x) he
    (weakSpanKanQuotientDiagram_initialVertexIso h x (transportSimplexIndex (n := ⦋0⦌) x))
    (fractionKanQuotientDiagram_initialVertexIso h x (transportSimplexIndex (n := ⦋0⦌) x))
  exact hc.trans (weakQuotientMappingComparison_native_component h x
    (transportSimplexIndex (n := ⦋0⦌) x))

/-- 元の恒等点の商上の比較像を戻すと、同じ native 恒等点と同じ strict Kan 比較辺との合成。 -/
theorem weakIdentityQuotientPointHom_native_comparison :
    weakIdentityQuotientPointHom h x ≫
      functorHomEvaluate (weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)) ≫
      (fractionIdentityQuotientValueIso h x).hom =
      weakIdentityNativePointHom h x ≫ Truncated.HomotopyCategory.homMk
        (weakSpanKanComparisonValueEdge h x (transportSimplexIndex (n := ⦋0⦌) x)).toTruncated := by
  have he := congrArg (fun m => weakIdentityNativePointHom h x ≫ m)
    (weakQuotientMappingComparison_identity_native h x)
  simpa only [weakIdentityQuotientPointHom, Category.assoc] using he

end SerrePositivity.KST.Fibration
