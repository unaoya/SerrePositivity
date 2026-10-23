module

public import SerrePositivity.InfinityCategories.F2.Compact.ClassificationTransport
public import SerrePositivity.InfinityCategories.F1.Yoneda.CovariantRepresentableInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafSliceComparison
public import SerrePositivity.InfinityCategories.F1.Transport.PointCoslicePostIso

/-!
概要：定義に用いた元の全共変 Hom 関手を、元の対象の coslice 射影の分類図式と比較。
方針：反転した表現可能前層の実 slice 比較を使い、二重反転を底と全空間で同時に戻す。
規約：元の covariantRepresentableInfinity と元の coslice を固定する。
使われ方：Yoneda 対象の compact 性のための全評価比較の入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の反転 slice の分類図式は、対応する元の coslice の分類図式と全自然同型。 -/
def oppositeSlice_classificationIso {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    FunctorIso
      (leftStraighteningInfinityDiagram
        (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm x))))
      (leftStraighteningInfinityDiagram
        (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x)))) :=
  leftClassification_overIso _ _
    ((Over.forget C.op).mapIso (cofinalPointSliceOverOpIso x))
    (cofinalPointSliceOverOpIso x).hom.w

/-- 元の全共変 Hom 関手は、元の対象からの coslice 自身を分類する図式。 -/
def covariantRepresentableInfinity_cosliceIso {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    FunctorIso (covariantRepresentableInfinity x)
      (leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm x))) := by
  let d : C ≅ C.op.op := (SSet.opFunctorCompOpFunctorIso.app C).symm
  let e := pointCoslicePostIso d x
  have he : e.hom ≫ sliceUnderProjection
      (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm x))) =
      sliceUnderProjection (SSet.yonedaEquiv.symm x) ≫ d.hom := by
    exact pointCoslicePostIso_projection d x
  have h := FunctorIso.precomp
    (representablePresheafInfinity_sliceIso (C := C.op) (SSet.opObjEquiv.symm x) ≪≫
    oppositeSlice_classificationIso (C := C.op) (SSet.opObjEquiv.symm x))
      ((SSet.uliftFunctor.{u + 1, u}).map d.hom)
  exact h ≪≫ leftClassification_squareIso
    (sliceUnderProjection (SSet.yonedaEquiv.symm x))
    (sliceUnderProjection
      (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm x)))) e d he

end SerrePositivity.InfinityCategories.F2.Compact
