module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanCanonicalDiagram
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagramEvaluation

/-!
概要：標準 span 比較の左右の実辺を、元の実分母・次辺の族へ照合する。
方針：境界 slice の左右制限と一点 slice の全辺表示を使う。
規約：分母・次辺の各頂点の選択ではなく、全単体の族を厳密に回収する。
使われ方：共通実分母上の回収族を、前段精密化と次辺の貼合せへ入力する。
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

/-- 一点への制限の元の全辺表示は、全錐比較の同じ辺への制限。 -/
lemma spanPointSliceRestrictionArrow {J X : SSet.{u}} (p : J ⟶ X)
    (j : (Δ[0] : SSet.{u}) ⟶ J) (r : (Δ[0] : SSet.{u}) ⟶ X) (h : j ≫ p = r) :
    sliceOverRestrict p j ≫ eqToHom (congrArg sliceOver h) ≫
      F2.Idempotent.pointSliceArrowMap r =
    sliceConeDiagramMap p ≫
      (pre ((joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 (Δ[0] : SSet.{u})) j)).app X := by
  subst r
  simp only [eqToHom_refl, Category.id_comp]
  rw [F2.Idempotent.pointSliceArrowMap, ← Category.assoc,
    spanSliceConeDiagramMap_restrict, Category.assoc, ← NatTrans.comp_app, ← pre_map]

lemma spanBoundarySliceLeft_arrow {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceLeft x y ≫ F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x) =
      sliceConeDiagramMap (intervalMappingBoundary x y) ≫
        (pre spanConeDenominatorInclusion).app X := by
  exact _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanPointSliceRestrictionArrow _ _ _ (intervalMappingBoundary_face_one x y)

/-- 全錐の形状内で、元の次辺に対応する辺。 -/
def spanConeNumeratorInclusion : (Δ[1] : SSet.{u}) ⟶
    join (Δ[0] : SSet.{u}) (boundary 1 : SSet.{u}) :=
  (joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (boundary.ι (0 : Fin 2))

lemma spanConeNumeratorInclusion_shape :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConeNumeratorInclusion.{u} ≫ spanBoundaryConeIso.hom = horn₂₀.ι₀₂ := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConeNumeratorInclusion, Category.assoc, spanBoundaryConeIso_right,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma spanBoundarySliceRight_arrow {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceRight x y ≫ F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm y) =
      sliceConeDiagramMap (intervalMappingBoundary x y) ≫
        (pre _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConeNumeratorInclusion).app X := by
  exact _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanPointSliceRestrictionArrow _ _ _ (intervalMappingBoundary_face_zero x y)

lemma verdierDenominatorSpanBoundaryIso_left
    {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundaryIso i x y).hom ≫
      (markedSpanSlice (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y).ι ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceLeft x y =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y ≫ (verdierDenominatorOver i x).ι := by
  have he : (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundarySliceIso i x y).hom ≫
      (markedSpanSlice (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y).ι =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice i x y).ι ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso x y).hom := rfl
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso i x y).hom).mp
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundaryIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]
  rw [he, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso_denominator, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceLeft_ι]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso_left]

lemma verdierDenominatorSpanBoundaryIso_right
    {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundaryIso i x y).hom ≫
      (markedSpanSlice (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y).ι ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceRight x y =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanNumerator i x y := by
  have he : (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundarySliceIso i x y).hom ≫
      (markedSpanSlice (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y).ι =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice i x y).ι ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso x y).hom := rfl
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso i x y).hom).mp
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundaryIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]
  rw [he, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso_numerator]
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceRight, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso_right]

/-- 標準比較の元の分母辺は、元の実分母の全辺表示と厳密に一致する。 -/
lemma verdierDenominatorSpanCanonicalComparison_denominator
    {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y ≫
      markedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) ≫ (pre horn₂₀.ι₀₁).app B.obj =
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y ≫ (verdierDenominatorOver i x).ι ≫
      F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x) := by
  have hd := congrArg (fun f => f ≫ (pre spanConeDenominatorInclusion).app B.obj)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison_diagram i x y)
  simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
    spanConeDenominatorInclusion_shape] at hd
  rw [hd, ← _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceLeft_arrow]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundaryIso_left i x y)

/-- 標準比較の元の次辺は、元の実次辺の全辺表示と厳密に一致する。 -/
lemma verdierDenominatorSpanCanonicalComparison_numerator
    {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y ≫
      markedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) ≫ (pre horn₂₀.ι₀₂).app B.obj =
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanNumerator i x y ≫
      F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm y) := by
  have hd := congrArg (fun f => f ≫ (pre _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConeNumeratorInclusion).app B.obj)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison_diagram i x y)
  simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConeNumeratorInclusion_shape] at hd
  rw [hd, ← _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceRight_arrow]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm y))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundaryIso_right i x y)

/-- 一点 slice の全辺表示の始点は、元の可変始域への射影。 -/
lemma spanPointSliceArrowMap_source {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) :
    F2.Idempotent.pointSliceArrowMap p ≫
      evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      sliceOverProjection p := by
  rw [F2.Idempotent.pointSliceArrowMap, Category.assoc, stable_pre_evaluateFunctorAt]
  change sliceConeDiagramMap p ≫ evaluateFunctorAt (Y := X)
    ((joinInl (Δ[0] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = _
  exact sliceConeDiagramMap_vertexEvaluation p

lemma spanPointSliceArrowMap_target {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) :
    F2.Idempotent.pointSliceArrowMap p ≫
      evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.const (p.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) := by
  have hc : sliceConeDiagramMap p ≫ coneRestriction (Δ[0] : SSet.{u}) X =
      SSet.const (functorVertex p) := by
    rw [sliceConeDiagramMap, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  rw [F2.Idempotent.pointSliceArrowMap, Category.assoc, stable_pre_evaluateFunctorAt]
  change sliceConeDiagramMap p ≫ evaluateFunctorAt (Y := X)
    ((joinInr (Δ[0] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = _
  rw [← stable_pre_evaluateFunctorAt, ← Category.assoc]
  change (sliceConeDiagramMap p ≫ coneRestriction (Δ[0] : SSet.{u}) X) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
  rw [hc, SSet.const_comp, evaluateFunctorAt_functorVertex]

/-- 共通実分母の fiber 上では、標準 span の分母辺の全族は同じ実分母に定値。 -/
lemma verdierDenominatorSpanCanonicalComparison_fiber_denominator
    {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y ≫
      markedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) ≫ (pre horn₂₀.ι₀₁).app B.obj =
    SSet.const (((verdierDenominatorOver i x).ι ≫
      F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x)).app
        (Opposite.op ⦋0⦌) d) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison_denominator,
    ← Category.assoc, vertexFiberι_comp, SSet.const_comp]

/-- 共通実分母上の実次辺の全族。 -/
def verdierDenominatorSpanFiberArrow {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ⟶
      (ihom (Δ[1] : SSet.{u})).obj B.obj :=
  vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanNumerator i x y ≫
    F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm y)

lemma verdierDenominatorSpanFiberArrow_source {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow i x y d ≫
      evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorOverSource i x).app (Opposite.op ⦋0⦌) d) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanPointSliceArrowMap_source, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpan_sharedSource]
  change vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorOverSource i x) = _
  rw [← Category.assoc, vertexFiberι_comp, SSet.const_comp]

lemma verdierDenominatorSpanFiberArrow_target {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow i x y d ≫
      evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.const y := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanPointSliceArrowMap_target, SSet.comp_const, SSet.comp_const]
  congr 1
  have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
  rw [hp, ← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceLeft_arrow := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceLeft_arrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceRight_arrow := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceRight_arrow

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConeNumeratorInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanConeNumeratorInclusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConeNumeratorInclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanConeNumeratorInclusion_shape := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConeNumeratorInclusion_shape

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanPointSliceArrowMap_source := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanPointSliceArrowMap_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanPointSliceArrowMap_target := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanPointSliceArrowMap_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanPointSliceRestrictionArrow := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanPointSliceRestrictionArrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanBoundaryIso_left := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundaryIso_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanBoundaryIso_right := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanBoundaryIso_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanCanonicalComparison_denominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison_denominator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanCanonicalComparison_fiber_denominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison_fiber_denominator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanCanonicalComparison_numerator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison_numerator

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanFiberArrow := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanFiberArrow_source := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanFiberArrow_target := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanConeNumeratorInclusion._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConeNumeratorInclusion._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanConeNumeratorInclusion.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConeNumeratorInclusion.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanFiberArrow.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow.eq_1
