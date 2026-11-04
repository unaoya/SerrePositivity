module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakIdentityScaffoldImage
public import SerrePositivity.KST.Fibration.VertexFiberBaseChangeHom

/-! # K-6 の恒等 span の同じ実 fiber 像を、既存の固定分数評価で回収する -/

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

/-- 同じ恒等 span の strict 評価像を、元の商像を底とする実 fiber 点で表示する。 -/
def weakIdentityScaffoldFiberImage :
    (vertexFiber (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
      (q.hom.app (Opposite.op ⦋0⦌) x)) _⦋0⦌ :=
  (eqToHom (congrArg (vertexFiber
    (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
    (congrArg (q.hom.app (Opposite.op ⦋0⦌))
      (transportSimplexFirstVertexMap_zeroIndex x)))).app (Opposite.op ⦋0⦌)
    ((cofinalVertexFiberBaseChangeIso
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
      (transportSimplexFirstVertexMap B.obj ≫ q.hom)
      (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x))).hom.app (Opposite.op ⦋0⦌)
      ((fractionCosliceFiberMap q.hom (weakEquivalences i) h.inverts x
        (transportSimplexFirstVertexMap B.obj)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x))).app (Opposite.op ⦋0⦌)
          (weakIdentitySimplexFiberPoint h x)))

/-- この同じ fiber 点は、既存の元の固定分数評価による恒等 span の像そのもの。 -/
theorem weakIdentityScaffoldFiberImage_eq_evaluation :
    weakIdentityScaffoldFiberImage h x =
      (fixedFractionCosliceEvaluation q.hom (weakEquivalences i) h.inverts x x).app
        (Opposite.op ⦋0⦌) (weakIdentityFixedSpan h x) := by
  let c := transportSimplexIndex (n := ⦋0⦌) x
  let T := eqToHom (congrArg (vertexFiber
    (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
    (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (transportSimplexFirstVertexMap_zeroIndex x)))
  have he := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (weakIdentitySimplexFiberPoint h x))
    (fractionCosliceFiberMap_unfixed q.hom (weakEquivalences i) h.inverts x
      (transportSimplexFirstVertexMap B.obj) (nerveVertex c))
  have hs : (fractionSourceFiberIso (weakEquivalences i) x
      (transportSimplexFirstVertexMap B.obj) (nerveVertex c)).inv.app (Opposite.op ⦋0⦌)
        (weakIdentitySimplexFiberPoint h x) = weakIdentityFixedSpanAtZeroIndex h x :=
    congrArg (fun m => m.app (Opposite.op ⦋0⦌) (weakIdentityFixedSpanAtZeroIndex h x))
      (weakSpanSimplexFiberIso i x c).hom_inv_id
  change _ = (fixedFractionCosliceEvaluation q.hom (weakEquivalences i) h.inverts x
    ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))).app
      (Opposite.op ⦋0⦌) _ at he
  have hv := congrArg ((fixedFractionCosliceEvaluation q.hom (weakEquivalences i) h.inverts x
    ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))).app
      (Opposite.op ⦋0⦌)) hs
  have hn := congrArg (T.app (Opposite.op ⦋0⦌)) (he.trans hv)
  have ht := fixedFractionCosliceEvaluation_transport_vertex q.hom (weakEquivalences i)
    h.inverts x (transportSimplexFirstVertexMap_zeroIndex x) (weakIdentityFixedSpan h x)
  unfold weakIdentityScaffoldFiberImage
  rw [cofinalVertexFiberBaseChangeIso_hom_eq]
  exact hn.trans ht

/-- 元の恒等 span の新分類で用いる実 fiber 点は、同じ coslice の恒等点と同型。 -/
def weakIdentityScaffoldFiberImage_identityIso :
    VertexIso (weakIdentityScaffoldFiberImage h x)
      (edgeToCosliceFiberVertex (SSet.Edge.id (q.hom.app (Opposite.op ⦋0⦌) x))) :=
  eqToIso (congrArg HomotopyCategory.mk (weakIdentityScaffoldFiberImage_eq_evaluation h x)) ≪≫
    identityFixedFractionCosliceEvaluationIso q.hom (weakEquivalences i) h.inverts x
      (weakIdentitySpan_mem h x)

end SerrePositivity.KST.Fibration
