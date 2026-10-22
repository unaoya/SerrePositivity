module
public import SerrePositivity.KST.Fibration.WeakIdentityScaffoldFiber
public import SerrePositivity.KST.Fibration.ScaffoldReconstructionFiberTransport
public import SerrePositivity.KST.Fibration.ScaffoldCosliceExtension

/-! # 元の K-6 恒等点の分類像を、指定 scaffold 復元の同じ coslice 恒等点と同定する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

private lemma classifyTransport {D : Type*} [Category D] {a b c d : D}
    (x : a ⟶ b) (e : b ≅ c) (t : c ≅ d) (y : a ⟶ c) (z : a ⟶ d)
    (he : x ≫ e.hom = y) (ht : y ≫ t.hom = z) :
    x ≫ (e ≪≫ t).hom = z := by
  simp only [Iso.trans_hom, ← Category.assoc]
  exact (congrArg (fun m => m ≫ t.hom) he).trans ht

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の native 比較像と指定分類成分は、同じ新復元恒等点の分類射を与える。 -/
theorem weakIdentityNativeComparisonImage_scaffold_pointHom :
    weakIdentityNativeComparisonImageHom h x ≫
      (fractionIdentityNativeClassificationIso (q := q) x).hom =
    cosliceFiberPointHom (smallUnstraighteningPointedImage
      (leftStraighteningInfinityDiagram
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
      (q.hom.app (Opposite.op ⦋0⦌) x)
      (scaffoldCosliceReconstructionPoint (q.hom.app (Opposite.op ⦋0⦌) x))) := by
  let b := q.hom.app (Opposite.op ⦋0⦌) x
  let p := sliceUnderProjection (yonedaEquiv.symm b)
  let c := transportSimplexIndex (n := ⦋0⦌) x
  let w := (cofinalVertexFiberBaseChangeIso p
    (transportSimplexFirstVertexMap B.obj ≫ q.hom) (nerveVertex c)).hom.app (Opposite.op ⦋0⦌)
    ((fractionCosliceFiberMap q.hom (weakEquivalences i) h.inverts x
      (transportSimplexFirstVertexMap B.obj) (nerveVertex c)).app (Opposite.op ⦋0⦌)
        (weakIdentitySimplexFiberPoint h x))
  have hr := weakIdentityNativeComparisonImage_scaffold_raw_pointHom h x
  have ht := scaffoldReconstructionFiberPoint_eqToHom_transport p
    (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (transportSimplexFirstVertexMap_zeroIndex x)) w
  have hn : weakIdentityNativeComparisonImageHom h x ≫
      (fractionIdentityNativeClassificationIso (q := q) x).hom =
      cosliceFiberPointHom (scaffoldReconstructionFiberPoint p b
        (weakIdentityScaffoldFiberImage h x)) :=
    classifyTransport _ _ _ _ _ hr ht
  have he := scaffoldReconstructionFiberPoint_pointHom_eq_of_vertexIso p b
    (weakIdentityScaffoldFiberImage_identityIso h x)
  have hi : scaffoldReconstructionFiberPoint p b (edgeToCosliceFiberVertex (SSet.Edge.id b)) =
      smallUnstraighteningPointedImage (leftStraighteningInfinityDiagram p) b
        (scaffoldCosliceReconstructionPoint b) :=
    congrArg (smallUnstraighteningPointedImage (leftStraighteningInfinityDiagram p) b)
      (scaffoldCosliceReconstructionPoint_fiberMap b).symm
  exact hn.trans (he.trans (congrArg cosliceFiberPointHom hi))

end SerrePositivity.KST.Fibration
