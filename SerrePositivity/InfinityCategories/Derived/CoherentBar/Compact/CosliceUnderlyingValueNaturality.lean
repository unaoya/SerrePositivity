module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.CosliceUnderlyingValueComparison
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence
/-!
概要：同じ coslice から基礎空間値への比較は、元の実辺輸送と可換する。
方針：fiber 射・宇宙交換・pointed 表示・実空間辺の四比較を合成する。
規約：選択した実輸送と実 spaceInfinityEdgeValue の両方を保持する。
使われ方：全基点チャートの transition と余錐の脚の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌)

/-- 始点固定 Tw の同じ fiber の、持ち上げた基礎空間値への比較。 -/
def dgBarCompactSourceUnderlyingValueComparison (y : C _⦋0⦌) :=
  (uliftVertexFiberIso.{u, u + 1} (twistedArrowSourceProjection x) y).hom ≫
    twistedArrowSourcePointedDisplayFiber x y ≫
      (pointedSpaceFiberValueEquivalence
        ((dgBarCompactUnderlyingValueFunctor x).app (Opposite.op ⦋0⦌) (ULift.up y))).hom

/-- 同じ実 native 辺の Kan 値への、始点固定 Tw の輸送比較。 -/
def dgBarCompactSourceUnderlyingValueComparison_transportIso
    {a b : C _⦋0⦌} (e : C.Edge a b) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
          (edgeTransport (twistedArrowSourceProjection x) e) ≫
        dgBarCompactSourceUnderlyingValueComparison x b)
      (dgBarCompactSourceUnderlyingValueComparison x a ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (F2.spaceInfinityEdgeValue
            ((SSet.Edge.ofTruncated (X := (SSet.uliftFunctor.{u + 1, u}).obj C)
              (uliftTruncatedEdge.{u, u + 1} e)).map
              (dgBarCompactUnderlyingValueFunctor x)))) := by
  let q := twistedArrowSourceProjection x
  let g := dgBarCompactUnderlyingValueFunctor x
  let eU := SSet.Edge.ofTruncated (X := (SSet.uliftFunctor.{u + 1, u}).obj C)
              (uliftTruncatedEdge.{u, u + 1} e)
  let va := (pointedSpaceFiberValueEquivalence (g.app (Opposite.op ⦋0⦌) (ULift.up a))).hom
  let vb := (pointedSpaceFiberValueEquivalence (g.app (Opposite.op ⦋0⦌) (ULift.up b))).hom
  have hU : FunctorIso
      ((uliftVertexFiberIso.{u, u + 1} q a).hom ≫ uliftFiberTransport q (edgeTransport q e))
      ((uliftVertexFiberIso.{u, u + 1} q a).hom ≫
        edgeTransport ((SSet.uliftFunctor.{u + 1, u}).map q) eU) :=
    ((edgeTransport_uliftIso.{u, u + 1} q e).precomp
      (uliftVertexFiberIso.{u, u + 1} q a).hom).symm
  have h₁ := hU.postcomp (twistedArrowSourcePointedDisplayFiber x b ≫ vb)
  simp only [uliftFiberTransport, Category.assoc, Iso.hom_inv_id_assoc] at h₁
  have h₂ := (dgLeftFibrationSquareTransportIso
    ((SSet.uliftFunctor.{u + 1, u}).map q) pointedSpaceProjection
    (twistedArrowSourcePointedDisplay x) g
    (twistedArrowSourcePointedDisplay_projection x) eU).precomp
      (uliftVertexFiberIso.{u, u + 1} q a).hom
  have h₂' := h₂.postcomp vb
  have hv : FunctorIso (edgeTransport pointedSpaceProjection (eU.map g) ≫ vb)
      (va ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (F2.spaceInfinityEdgeValue (eU.map g))) :=
    (F2.spaceInfinityEdgeTransportValueIso (eU.map g)).symm
  have h₃ := hv.precomp
    ((uliftVertexFiberIso.{u, u + 1} q a).hom ≫ twistedArrowSourcePointedDisplayFiber x a)
  have hF (y : C _⦋0⦌) : transportSquareFiberMap
      ((SSet.uliftFunctor.{u + 1, u}).map q) pointedSpaceProjection
      (twistedArrowSourcePointedDisplay x) g
      (twistedArrowSourcePointedDisplay_projection x) (ULift.up y) =
        twistedArrowSourcePointedDisplayFiber x y := rfl
  rw [hF, hF] at h₂'
  simp only [Category.assoc] at h₁ h₂' h₃
  simpa only [dgBarCompactSourceUnderlyingValueComparison, Category.assoc] using
    h₁.trans (h₂'.trans h₃)

/-- 同じ coslice の元の輸送と、同じ基礎空間関手の実辺作用の比較。 -/
def dgBarCompactCosliceUnderlyingValueComparison_transportIso
    {a b : C _⦋0⦌} (e : C.Edge a b) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
          (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e) ≫
        dgBarCompactCosliceUnderlyingValueComparison x b)
      (dgBarCompactCosliceUnderlyingValueComparison x a ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (F2.spaceInfinityEdgeValue
            ((SSet.Edge.ofTruncated (X := (SSet.uliftFunctor.{u + 1, u}).obj C)
              (uliftTruncatedEdge.{u, u + 1} e)).map
              (dgBarCompactUnderlyingValueFunctor x)))) := by
  have h₁ := (leftFibrationMap_transportIso
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) (twistedArrowSourceProjection x)
    (cosliceToTwistedArrowSource x) (cosliceToTwistedArrowSource_projection x) e).ulift.{u, u + 1}
  have h₂ := (dgBarCompactSourceUnderlyingValueComparison_transportIso x e).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map (dgBarCompactCosliceSourceFiberMap x a))
  have h₁' := h₁.postcomp (dgBarCompactSourceUnderlyingValueComparison x b)
  simp only [Functor.map_comp, Category.assoc] at h₁' h₂
  simpa only [dgBarCompactCosliceUnderlyingValueComparison,
    dgBarCompactSourceUnderlyingValueComparison, dgBarCompactCosliceSourceFiberMap,
    Category.assoc] using h₁'.trans h₂

end SerrePositivity.InfinityCategories
