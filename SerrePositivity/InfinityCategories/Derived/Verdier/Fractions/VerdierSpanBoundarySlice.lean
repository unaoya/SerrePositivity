module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierDenominatorSpanSlice
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanSliceComparison
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceDiagramConeMap
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence

/-!
概要：実分母・次辺の二点表示を、元の区間境界上の実 marked slice へ移す。
方針：二点 coproduct の同型で図式と実錐を輸送し、同じ左脚を厳密に照合する。
規約：実分母条件の一致を証明し、追加入力にしない。
使われ方：実分母添字上の族と元の固定端点 span の全関手比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

lemma spanEndpointCoproductDiagram_eq {X : SSet.{u}} (x y : X _⦋0⦌) :
    spanTwoPointDiagram x y ≫ (Iso.refl X).hom =
      spanEndpointCoproductIso.hom ≫ intervalMappingBoundary x y := by
  apply coprod.hom_ext
  · simp only [spanTwoPointDiagram, Iso.refl_hom, Category.comp_id, coprod.inl_desc,
      ← Category.assoc, spanEndpointCoproductIso_left, intervalMappingBoundary_face_one]
  · simp only [spanTwoPointDiagram, Iso.refl_hom, Category.comp_id, coprod.inr_desc,
      ← Category.assoc, spanEndpointCoproductIso_right, intervalMappingBoundary_face_zero]

/-- 同じ二終点の二点表示と、元の区間境界表示の実 slice の厳密同型。 -/
def spanBoundarySliceIso {X : SSet.{u}} (x y : X _⦋0⦌) :
    sliceOver (spanTwoPointDiagram x y) ≅ sliceOver (intervalMappingBoundary x y) :=
  F1B.sliceDiagramIso spanEndpointCoproductIso (Iso.refl X) _ _
    (spanEndpointCoproductDiagram_eq x y)

lemma spanBoundarySliceIso_val {X : SSet.{u}} (x y : X _⦋0⦌)
    (c : JoinCone (spanTwoPointDiagram x y)) :
    ((spanBoundarySliceIso x y).hom.app (Opposite.op ⦋0⦌) c).val =
      joinMap (𝟙 (Δ[0] : SSet.{u})) spanEndpointCoproductIso.inv ≫ c.val := by
  simpa only [spanBoundarySliceIso, Iso.refl_hom, Category.comp_id] using
    F1B.sliceDiagramIso_hom_val spanEndpointCoproductIso
    (Iso.refl X) _ _ (spanEndpointCoproductDiagram_eq x y) c

lemma spanBoundarySliceIso_denominator_edge {X : SSet.{u}} (x y : X _⦋0⦌)
    (c : JoinCone (spanTwoPointDiagram x y)) :
    intervalFunctorVertexEdge
      ((sliceConeFamilyMap (intervalMappingBoundary x y) ≫ spanConeDenominatorFamily x y).app
        (Opposite.op ⦋0⦌) ((spanBoundarySliceIso x y).hom.app (Opposite.op ⦋0⦌) c)) =
      (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x)
        ((sliceOverCoproductLeft (SSet.yonedaEquiv.symm x)
          (SSet.yonedaEquiv.symm y)).app (Opposite.op ⦋0⦌) c)).edge := by
  let w := (spanBoundarySliceIso x y).hom.app (Opposite.op ⦋0⦌) c
  change intervalFunctorVertexEdge (((pre spanConeDenominatorInclusion).app X).app
    (Opposite.op ⦋0⦌) ((sliceConeFamilyMap (intervalMappingBoundary x y)).app
      (Opposite.op ⦋0⦌) w).val) = _
  rw [sliceConeFamilyMap_app_zero]
  change intervalFunctorVertexEdge (functorVertex (spanConeDenominatorInclusion ≫ w.val)) = _
  rw [intervalFunctorVertexEdge_functorVertex]
  change SSet.yonedaEquiv (spanConeDenominatorInclusion ≫ w.val) =
    SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      ((sliceOverCoproductLeft (SSet.yonedaEquiv.symm x)
        (SSet.yonedaEquiv.symm y)).app (Opposite.op ⦋0⦌) c).val)
  rw [sliceOverCoproductLeft_vertex_val]
  dsimp only [w]
  rw [spanBoundarySliceIso_val, spanConeDenominatorInclusion]
  have he : boundary.ι (1 : Fin 2) ≫ spanEndpointCoproductIso.inv =
      (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) := by
    rw [← spanEndpointCoproductIso_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc]
  rw [← Category.assoc (joinMap (𝟙 (Δ[0] : SSet.{u})) (boundary.ι (1 : Fin 2))),
    ← joinMap_comp, Category.id_comp, he]

/-- 同じ元の実分母条件を保持した、二点表示から区間境界表示への厳密同型。 -/
def verdierDenominatorSpanBoundarySliceIso {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : (verdierDenominatorSpanSlice i x y : SSet.{u}) ≅
      (markedSpanSlice (weakEquivalences i) x y : SSet.{u}) :=
  fullSubcomplexIso (spanBoundarySliceIso x y) _ _ (by
    intro v
    change (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x)
      ((sliceOverCoproductLeft (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)).app
        (Opposite.op ⦋0⦌) v)).edge ∈ weakEquivalences i ↔ _
    rw [spanBoundarySliceIso_denominator_edge])

/-- 実分母・次辺の全空間から、同じ二終点上の実 slice への厳密同型。 -/
def verdierDenominatorSpanBoundaryIso {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ≅
      (markedSpanSlice (weakEquivalences i) x y : SSet.{u}) :=
  (verdierDenominatorSpanSliceIso i x y).symm ≪≫ verdierDenominatorSpanBoundarySliceIso i x y

/-- 元の実 slice の比較による、実分母・次辺族から固定端点 span への標準比較。 -/
def verdierDenominatorSpanCanonicalComparison {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ⟶
      fixedMarkedSpans B.obj (weakEquivalences i) x y :=
  (verdierDenominatorSpanBoundaryIso i x y).hom ≫
    markedSpanSliceToFixed (weakEquivalences i) x y

/-- 元の実分母・次辺族と固定端点 span の標準比較は、全写像空間で同値。 -/
lemma verdierDenominatorSpanCanonicalComparison_isQCatEquivalence
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    IsQCatEquivalence (verdierDenominatorSpanCanonicalComparison i x y) :=
  (qCatEquivalenceOfIso (verdierDenominatorSpanBoundaryIso i x y)).isQCatEquivalence.comp
    (markedSpanSliceToFixed_isQCatEquivalence h x y)

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceIso_denominator_edge := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso_denominator_edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceIso_val := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso_val

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanEndpointCoproductDiagram_eq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanEndpointCoproductDiagram_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundaryIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanBoundaryIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundaryIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundarySliceIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanBoundarySliceIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundarySliceIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanCanonicalComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanCanonicalComparison_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceIso.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanBoundarySliceIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundarySliceIso._proof_1
