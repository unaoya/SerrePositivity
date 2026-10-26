module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxCoordinateTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxRawInputActions
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxBaseCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputStrictEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedDiagonalInputPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.EndpointTransportComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPostEndpointNaturality
/-!
概要：元 lax 比較と入力付き厳密模型の比較を、矢印座標と元左右 Hom 入力で厳密に同定する。
方針：同じ実比較の全射影・端点輸送・全入力を保持する。
規約：新たな主経路仮定を置かない。使われ方：K-S• の全 lax 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
variable (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
local notation "eX" => dgGluingHomTargetAugmentationEdge R C D E p q X
local notation "eY" => dgGluingHomTargetAugmentationEdge R C D E p q Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetLaxHomCoordinateComparison_arrow :
    dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      dgGluingHomTargetLaxHomCoordinateTransport R C D E p q X Y ≫
        dgGluingHomTargetInputCoordinateArrowProjection R C D E p q X Y =
    dgGluingHomTargetArrowCompositionComparison R C D E p q X Y := by
  rw [dgGluingHomTargetLaxHomCoordinateTransport, Category.assoc,
    dgGluingHomTargetLaxHomCoordinateTargetIso_arrow,
    reassoc_of% dgGluingHomTargetLaxHomPinchedIntervalTransport_arrow,
    dgGluingHomTargetLaxHomIntervalArrowCoordinateIso,
    dgGluingArrowCoordinateIso, Iso.trans_hom, Iso.symm_hom]
  erw [← reassoc_of% pinchedInterval_endpoint]
  have hcast :
      (pinchedEndpointIso
        (dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q X)
        (dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q Y)).hom =
      (dgGluingHomTargetLaxArrowEndpointIso R C D E p q X Y).hom ≫
        (pinchedEndpointIso (dgGluingHomTargetArrowDiagram_vertex R C D E p q X)
          (dgGluingHomTargetArrowDiagram_vertex R C D E p q Y)).hom := by
    rw [dgGluingHomTargetLaxArrowEndpointIso, dgGluingPinchedCompositeIso,
      dgGluingPinchedEndpointIso_trans]
  erw [reassoc_of% hcast,
    reassoc_of% dgGluingHomTargetLaxHomPullbackComparison_arrow_transport]
  rfl

lemma dgGluingHomTargetLaxHomCoordinateComparison_inputs :
    dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      dgGluingHomTargetLaxHomCoordinateTransport R C D E p q X Y ≫
        dgGluingHomTargetInputCoordinateInputsProjection R C D E p q X Y =
    lift (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y))
      (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y)) := by
  rw [dgGluingHomTargetLaxHomCoordinateTransport, Category.assoc,
    dgGluingHomTargetLaxHomCoordinateTargetIso_inputs,
    reassoc_of% dgGluingHomTargetLaxHomPinchedIntervalTransport_inputs,
    dgGluingHomTargetLaxHomPullbackComparison_raw_inputs]

lemma dgGluingHomTargetLaxHomCoordinateTransport_comparison :
    dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      dgGluingHomTargetLaxHomCoordinateTransport R C D E p q X Y =
    dgGluingHomTargetInputCoordinateComparison R C D E p q X Y := by
  apply pullback.hom_ext
  · exact (dgGluingHomTargetLaxHomCoordinateComparison_arrow R C D E p q X Y).trans
      (dgGluingHomTargetInputCoordinateComparison_arrow R C D E p q X Y).symm
  · exact (dgGluingHomTargetLaxHomCoordinateComparison_inputs R C D E p q X Y).trans
      (dgGluingHomTargetInputCoordinateComparison_inputs R C D E p q X Y).symm

end SerrePositivity.InfinityCategories
