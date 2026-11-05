module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxVertices
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomMappingModel
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionIsoNaturality
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFamilyVertexEdge
/-!
概要：元終域の指定 augmentation 全族の実 Hom を、同じ二合成対角へ移す。
方針：元頂点辺を回収し、実 pinched Hom と矢印 Hom の合成表示を使う。
規約：指定全族の実作用を変えない。使われ方：元 lax Hom 比較の正規化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
variable (X : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

def dgGluingHomTargetArrowDiagram : (Δ[1] : SSet.{max (u + 1) v}) ⟶ dgNerve R E :=
  SSet.yonedaEquiv.symm (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)).edge

lemma dgGluingHomTargetArrowDiagram_vertex :
    (dgGluingHomTargetAugmentationArrowFamily R C D E p q).app (Opposite.op ⦋0⦌)
      (Simplex.vertex X) = functorVertex (dgGluingHomTargetArrowDiagram R C D E p q X) := by
  apply intervalFunctorVertexEdge_injective
  rw [dgGluingHomTargetAugmentationArrowFamily, dgGluingCurryHomotopy_vertex_edge,
    dgGluingHomTargetAugmentationHomotopy_vertex_edge,
    intervalFunctorVertexEdge_functorVertex, dgGluingHomTargetArrowDiagram,
    Equiv.apply_symm_apply]

variable (Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

def dgGluingHomTargetArrowIntervalComparison :
    complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y) ⟶
      intervalMappingSpace
        (functorVertex (dgGluingHomTargetArrowDiagram R C D E p q X))
        (functorVertex (dgGluingHomTargetArrowDiagram R C D E p q Y)) :=
  (dgGluingHomMappingIso R C D M X Y).inv ≫
    pinchedHomMap (dgGluingHomTargetAugmentationArrowFamily R C D E p q)
      (Simplex.vertex X) (Simplex.vertex Y) ≫
    (pinchedEndpointIso (dgGluingHomTargetArrowDiagram_vertex R C D E p q X)
      (dgGluingHomTargetArrowDiagram_vertex R C D E p q Y)).hom ≫
    pinchedHomToIntervalMappingSpace _ _

def dgGluingHomTargetArrowCompositionComparison :=
  dgGluingHomTargetArrowIntervalComparison R C D E p q X Y ≫
    (dgGluingArrowCompositionIso
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))).inv

end SerrePositivity.InfinityCategories
