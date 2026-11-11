module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetLaxCoordinateTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetLaxRawInputActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetLaxBaseCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetInputStrictEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RestrictedDiagonalInputPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.EndpointTransportComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IntervalPostEndpointNaturality
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
local notation "eX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationEdge R C D E p q X
local notation "eY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationEdge R C D E p q Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetLaxHomCoordinateComparison_arrow :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomCoordinateTransport R C D E p q X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputCoordinateArrowProjection R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowCompositionComparison R C D E p q X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomCoordinateTransport, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomCoordinateTargetIso_arrow,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPinchedIntervalTransport_arrow,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalArrowCoordinateIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCoordinateIso, Iso.trans_hom, Iso.symm_hom]
  erw [← reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedInterval_endpoint]
  have hcast :
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q Y)).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxArrowEndpointIso R C D E p q X Y).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowDiagram_vertex R C D E p q X)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowDiagram_vertex R C D E p q Y)).hom := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxArrowEndpointIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedCompositeIso,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedEndpointIso_trans]
  erw [reassoc_of% hcast,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullbackComparison_arrow_transport]
  rfl

lemma dgGluingHomTargetLaxHomCoordinateComparison_inputs :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomCoordinateTransport R C D E p q X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputCoordinateInputsProjection R C D E p q X Y =
    lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomCoordinateTransport, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomCoordinateTargetIso_inputs,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPinchedIntervalTransport_inputs,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullbackComparison_raw_inputs]

lemma dgGluingHomTargetLaxHomCoordinateTransport_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomCoordinateTransport R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputCoordinateComparison R C D E p q X Y := by
  apply pullback.hom_ext
  · exact (dgGluingHomTargetLaxHomCoordinateComparison_arrow R C D E p q X Y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputCoordinateComparison_arrow R C D E p q X Y).symm
  · exact (dgGluingHomTargetLaxHomCoordinateComparison_inputs R C D E p q X Y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputCoordinateComparison_inputs R C D E p q X Y).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
