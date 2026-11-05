module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomIntervalArrowCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPostEndpointNaturality
/-!
概要：正本の底の区間 Hom を元の二つの導来 Hom の積へ厳密に移す。
方針：矢印頂点の端点を同じ augmentation 辺で正規化し、積の区間 Hom 同型を適用する。
規約：元の二端点と二作用の順序を保持する。
使われ方：正本標的の二つの底写像を入力付き四座標標的の二脚へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
lemma dgGluingLaxHomIntervalBaseVertex (X : DGGluingObject R C D M) :
    (F2.arrowEndpointPair
      ((SSet.uliftFunctor.{max (u + 1) v w,max (u + 1) v}).obj
        (dgModuleDerivedInfinityCategory R C))).app (Opposite.op ⦋0⦌)
      (dgGluingLaxHomArrowVertex R C D M X) =
    ((dgGluingUniverseDerivedYoneda.{u,v,w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex (A := R) X.left)),
      (dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex (A := R) X.right))) := by
  exact (congrArg ((F2.arrowEndpointPair
    ((SSet.uliftFunctor.{max (u + 1) v w,max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C))).app (Opposite.op ⦋0⦌))
    (dgGluingLaxHomArrowVertex_diagram R C D M X)).trans
      (dgGluingArrowEndpointPair_vertex (dgGluingDerivedAugmentationEdge R C D M X))

def dgGluingLaxHomIntervalBaseCoordinateIso (X Y : DGGluingObject R C D M) :=
  intervalEndpointIso (dgGluingLaxHomIntervalBaseVertex R C D M X)
    (dgGluingLaxHomIntervalBaseVertex R C D M Y) ≪≫
      (dgGluingIntervalMappingProductIso
        ((dgGluingUniverseDerivedYoneda.{u,v,w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (Simplex.vertex (A := R) X.left)))
        ((dgGluingUniverseDerivedYoneda.{u,v,w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (Simplex.vertex (A := R) Y.left)))
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (Simplex.vertex (A := R) X.right)))
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (Simplex.vertex (A := R) Y.right)))).symm

lemma dgGluingLaxHomIntervalEndpointMap_coordinates (X Y : DGGluingObject R C D M) :
    (dgGluingLaxHomIntervalArrowCoordinateIso R C D M X Y).inv ≫
      dgGluingLaxHomIntervalEndpointMap R C D M X Y ≫
        (dgGluingLaxHomIntervalBaseCoordinateIso R C D M X Y).hom =
      dgGluingArrowCompositionEndpointPair (dgGluingDerivedAugmentationEdge R C D M X)
        (dgGluingDerivedAugmentationEdge R C D M Y) := by
  rw [dgGluingLaxHomIntervalArrowCoordinateIso, Iso.trans_inv, Iso.symm_inv,
    dgGluingLaxHomIntervalBaseCoordinateIso, Iso.trans_hom,
    dgGluingLaxHomIntervalEndpointMap]
  simp only [Category.assoc]
  rw [reassoc_of% dgGluingIntervalPostOfEq_endpoint_naturality]
  change (dgGluingArrowCompositionIso (dgGluingDerivedAugmentationEdge R C D M X)
    (dgGluingDerivedAugmentationEdge R C D M Y)).hom ≫
      dgGluingArrowIntervalEndpointPair (dgGluingDerivedAugmentationEdge R C D M X)
        (dgGluingDerivedAugmentationEdge R C D M Y) = _
  exact dgGluingArrowCompositionIso_hom_endpoints _ _
end SerrePositivity.InfinityCategories
