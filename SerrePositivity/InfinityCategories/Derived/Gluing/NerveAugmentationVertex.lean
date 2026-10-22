module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NerveLaxComparison
public import SerrePositivity.InfinityCategories.Derived.HomotopyPrecompVertex

/-! lax pullback 比較に用いた構造変換の各頂点辺は、同じ元の augmentation。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C] [DGCategory R D]
  (M : Bimodule R C D)

lemma dgGluingAugmentationNerveHomotopy_vertex_edge
    (X : DGGluingObject R C D M) :
    (simplicialHomotopyVertexEdge (dgGluingAugmentationNerveHomotopy R C D M)
      (Simplex.vertex X)).edge =
    (dgClosedEdge R (RightModule R C) (dgGluingAugmentation R C D M X)).edge := by
  change (simplicialHomotopyVertexEdge
    (functorHomotopyPrecomp
      (dgCommaAugmentationUnliftedHomotopy R D (RightModule R C) M.toFunctor)
      (dgNerve.map (dgGluingToComma R C D M))) (Simplex.vertex X)).edge = _
  rw [simplicialHomotopyVertexEdge_precomp_edge]
  have hx : (dgNerve.map (dgGluingToComma R C D M)).app
      (Opposite.op ⦋0⦌) (Simplex.vertex X) =
      Simplex.vertex (dgGluingCommaObject R C D M X) := by
    apply (Simplex.vertexEquiv (A := R)
      (D := DGFunctorCommaObject R D (RightModule R C) M.toFunctor)).injective
    rfl
  rw [hx]
  exact dgCommaAugmentationUnliftedHomotopy_vertex_edge R D (RightModule R C)
    M.toFunctor (dgGluingCommaObject R C D M X)

end SerrePositivity.InfinityCategories
