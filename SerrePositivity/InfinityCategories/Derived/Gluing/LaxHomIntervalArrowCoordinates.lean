module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomPinchedIntervalTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.EndpointTransportComposition
/-!
概要：正本の区間矢印座標を同じ二合成対応へ厳密に移す。
方針：元矢印頂点と augmentation 図式の一致を端点輸送へ渡す。
規約：元の全区間族を保持し、公開正本比較の型を変更しない。
使われ方：入力付き四座標比較との厳密な可換性を証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingLaxHomArrowVertex_diagram (X : DGGluingObject R C D M) :
    dgGluingLaxHomArrowVertex R C D M X =
      functorVertex (dgGluingDerivedAugmentationArrowDiagram R C D M X) := by
  have hc := congrArg (fun k => k.app (Opposite.op ⦋0⦌)
    (ULift.up (Simplex.vertex (A := R) X)))
    (dgGluingUniverseDerivedNerveLaxComparison_arrow R C D M)
  exact hc.trans (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M X)

def dgGluingLaxHomIntervalArrowCoordinateIso (X Y : DGGluingObject R C D M) :=
  intervalEndpointIso (dgGluingLaxHomArrowVertex_diagram R C D M X)
    (dgGluingLaxHomArrowVertex_diagram R C D M Y) ≪≫
    (dgGluingArrowCompositionIso (dgGluingDerivedAugmentationEdge R C D M X)
      (dgGluingDerivedAugmentationEdge R C D M Y)).symm

lemma dgGluingLaxHomIntervalArrowCoordinateIso_comparison (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomPullbackComparison R C D M X Y ≫
      dgGluingLaxHomPinchedIntervalTransport R C D M X Y ≫ pullback.fst _ _ ≫
        (dgGluingLaxHomIntervalArrowCoordinateIso R C D M X Y).hom =
      dgGluingLaxHomArrowCompositionComparison R C D M X Y := by
  rw [reassoc_of% dgGluingLaxHomPinchedIntervalTransport_arrow,
    dgGluingLaxHomIntervalArrowCoordinateIso, Iso.trans_hom,
    dgGluingLaxHomArrowCompositionComparison, dgGluingLaxHomArrowIntervalComparison]
  simp only [Category.assoc]
  congr 1
  rw [← reassoc_of% pinchedInterval_endpoint]
  rw [← reassoc_of% dgGluingPinchedEndpointIso_trans]
  rfl
end SerrePositivity.InfinityCategories
