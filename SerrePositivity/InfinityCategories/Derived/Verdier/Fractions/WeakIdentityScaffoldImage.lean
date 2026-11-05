module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の恒等 span の strict Kan 比較像を、新分類で同じ実 fiber 像へ送る。 -/
theorem weakIdentityNativeComparisonImage_scaffold_raw_pointHom :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageHom h x ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso q.hom x
        (transportSimplexIndex (n := ⦋0⦌) x)).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
      (q.hom.app (Opposite.op ⦋0⦌)
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
          (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x))))
      ((cofinalVertexFiberBaseChangeIso
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
        (transportSimplexFirstVertexMap B.obj ≫ q.hom)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x))).hom.app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionCosliceFiberMap q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x
          (transportSimplexFirstVertexMap B.obj)
          (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x))).app (Opposite.op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentitySimplexFiberPoint h x)))) := by
  let c := transportSimplexIndex (n := ⦋0⦌) x
  let p := sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))
  let k := transportSimplexFirstVertexMap B.obj ≫ q.hom
  let f := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionCosliceBaseChange q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x
    (transportSimplexFirstVertexMap B.obj)
  have hf : f ≫ pullback.snd p k = _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection i x :=
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionCosliceBaseChange_snd q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x _
  have he := scaffoldCocartesianPostBaseChangeClassification_pointHom
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection i x) p k f hf c (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityStrictSectionPoint h x)
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityStrictSectionPoint_evaluate] at he
  change _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImageHom h x ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso q.hom x c).hom = _
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanSimplexClassificationValueIso, Iso.trans_hom, Iso.symm_hom,
    _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate]
  exact he

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityNativeComparisonImage_scaffold_raw_pointHom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityNativeComparisonImage_scaffold_raw_pointHom
