module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldCocartesianPostBaseChange
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionIdentityClassificationComponent
public import SerrePositivity.KST.Fibration.ScaffoldCocartesianBaseChange
public import SerrePositivity.KST.Fibration.ScaffoldCocartesianPostBaseChange

/-! # K-6 の元の恒等 span 比較像を、同じ scaffold 分類成分で計算する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の恒等 span の strict Kan 比較像を、新分類で同じ実 fiber 像へ送る。 -/
theorem weakIdentityNativeComparisonImage_scaffold_raw_pointHom :
    weakIdentityNativeComparisonImageHom h x ≫
      (fractionKanSimplexClassificationValueIso q.hom x
        (transportSimplexIndex (n := ⦋0⦌) x)).hom =
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
      (q.hom.app (Opposite.op ⦋0⦌)
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
          (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x))))
      ((cofinalVertexFiberBaseChangeIso
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
        (transportSimplexFirstVertexMap B.obj ≫ q.hom)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x))).hom.app (Opposite.op ⦋0⦌)
        ((fractionCosliceFiberMap q.hom (weakEquivalences i) h.inverts x
          (transportSimplexFirstVertexMap B.obj)
          (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x))).app (Opposite.op ⦋0⦌)
            (weakIdentitySimplexFiberPoint h x)))) := by
  let c := transportSimplexIndex (n := ⦋0⦌) x
  let p := sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))
  let k := transportSimplexFirstVertexMap B.obj ≫ q.hom
  let f := fractionCosliceBaseChange q.hom (weakEquivalences i) h.inverts x
    (transportSimplexFirstVertexMap B.obj)
  have hf : f ≫ pullback.snd p k = weakSpanSimplexProjection i x :=
    fractionCosliceBaseChange_snd q.hom (weakEquivalences i) h.inverts x _
  have he := scaffoldCocartesianPostBaseChangeClassification_pointHom
    (weakSpanSimplexProjection i x) p k f hf c (weakIdentityStrictSectionPoint h x)
  rw [weakIdentityStrictSectionPoint_evaluate] at he
  change weakIdentityNativeComparisonImageHom h x ≫
      (fractionKanSimplexClassificationValueIso q.hom x c).hom = _
  simp only [fractionKanSimplexClassificationValueIso, Iso.trans_hom, Iso.symm_hom,
    functorIso_app_hom_evaluate]
  exact he

end SerrePositivity.KST.Fibration
