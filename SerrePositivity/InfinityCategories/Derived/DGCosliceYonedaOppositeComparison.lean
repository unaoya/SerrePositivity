module
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetSpaceComparison
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafSliceComparison
/-!
概要：反対圏の coslice の Yoneda 評価を、元の F1 表現可能前層に比較する。
方針：元の coslice の表現を実分類関手へ送り、右 slice の反転同型を使う。
規約：元の共同 Hom 評価の制限そのものへ接続する。使われ方：実反変 Hom の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
/-- 元の coslice の Yoneda 評価と同じ実射影の分類図式の比較。 -/
def dgCosliceYonedaClassificationIso :
    FunctorIso (dgCosliceYonedaSpaceInfinity X x)
      (leftStraighteningInfinityDiagram
        (sliceUnderProjection (SSet.yonedaEquiv.symm x))) :=
  (leftStraighteningInfinityDiagram_representationIso _
    (dgCosliceYonedaTransportRepresentation X x)).symm
/-- 反対圏の coslice の全関手は元の F1 表現可能前層と同型。 -/
def dgOppositeCosliceYonedaSpaceIso :
    FunctorIso (dgCosliceYonedaSpaceInfinity X.op (SSet.opObjEquiv.symm x))
      (representablePresheafInfinity x) := by
  let e := cofinalPointSliceOverOpIso x
  have h := leftFibrationInfinityVertexIsoOfPrecompositionEquivalence
    (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm x)))
    (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x)))
    e.hom.left e.hom.w
    (isPrecompositionEquivalence_of_iso ((Over.forget X.op).mapIso e))
  have h' := VertexIso.map h (leftStraighteningInfinityMap X.op)
  rw [← leftStraighteningInfinityDiagram_vertex,
    ← leftStraighteningInfinityDiagram_vertex] at h'
  exact dgCosliceYonedaClassificationIso X.op (SSet.opObjEquiv.symm x) ≪≫ h'.symm ≪≫
    (representablePresheafInfinity_sliceIso x).symm
end SerrePositivity.InfinityCategories
