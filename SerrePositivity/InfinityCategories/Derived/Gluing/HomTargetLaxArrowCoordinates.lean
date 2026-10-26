module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCoordinateEndpointIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxIntervalTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.EndpointTransportComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPostEndpointNaturality
/-!
概要：元 lax Hom の矢印と底の区間座標を、同じ二合成対応へ厳密に移す。
方針：元の比較辺と矢印頂点の全等式を端点輸送へ渡す。
規約：全区間族を保持する。使われ方：元二脚比較の標的座標同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
variable (X : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

abbrev dgGluingHomTargetAugmentationEdge :
    (dgNerve R E).Edge (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj X.right)) :=
  Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X))

lemma dgGluingHomTargetLaxHomIntervalBaseVertex :
    (F2.arrowEndpointPair (dgNerve R E)).app (Opposite.op ⦋0⦌)
      (dgGluingHomTargetLaxHomArrowVertex R C D E p q X) =
    (Simplex.vertex (p.obj X.left), Simplex.vertex (q.obj X.right)) := by
  exact (congrArg ((F2.arrowEndpointPair (dgNerve R E)).app (Opposite.op ⦋0⦌))
    (dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q X)).trans
      (dgGluingArrowEndpointPair_vertex (dgGluingHomTargetAugmentationEdge R C D E p q X))

variable (Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetLaxHomIntervalArrowCoordinateIso :=
  dgGluingArrowCoordinateIso
    (dgGluingHomTargetAugmentationEdge R C D E p q X)
    (dgGluingHomTargetAugmentationEdge R C D E p q Y)
    (dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q X)
    (dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q Y)

def dgGluingHomTargetLaxHomIntervalBaseCoordinateIso :=
  dgGluingArrowBaseCoordinateIso
    (dgGluingHomTargetAugmentationEdge R C D E p q X)
    (dgGluingHomTargetAugmentationEdge R C D E p q Y)
    (dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q X)
    (dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q Y)

lemma dgGluingHomTargetLaxHomIntervalEndpointMap_coordinates :
    (dgGluingHomTargetLaxHomIntervalArrowCoordinateIso R C D E p q X Y).inv ≫
      dgGluingHomTargetLaxHomIntervalEndpointMap R C D E p q X Y ≫
        (dgGluingHomTargetLaxHomIntervalBaseCoordinateIso R C D E p q X Y).hom =
    dgGluingArrowCompositionEndpointPair (dgGluingHomTargetAugmentationEdge R C D E p q X)
      (dgGluingHomTargetAugmentationEdge R C D E p q Y) :=
  dgGluingArrowCoordinateIso_endpoints
    (dgGluingHomTargetAugmentationEdge R C D E p q X)
    (dgGluingHomTargetAugmentationEdge R C D E p q Y)
    (dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q X)
    (dgGluingHomTargetLaxHomArrowVertex_diagram R C D E p q Y)

end SerrePositivity.InfinityCategories
