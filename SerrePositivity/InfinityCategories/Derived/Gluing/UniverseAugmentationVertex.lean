module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseAugmentationPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrismUnitEdge

/-! 共通単体宇宙へ移した構造変換の実頂点辺も、元の augmentation の持ち上げ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseAugmentationHomotopy_vertex_edge
    (X : DGGluingObject R C D M) :
    (simplicialHomotopyVertexEdge (dgGluingUniverseAugmentationHomotopy R C D M)
      (ULift.up (Simplex.vertex X))).edge =
    ULift.up (dgClosedEdge R (RightModule R C) (dgGluingAugmentation R C D M X)).edge := by
  change (dgGluingUniverseAugmentationPrism R C D M).app (Opposite.op ⦋1⦌)
    ((Truncated.Edge.id (X := (truncation 2).obj
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (dgNerve R (DGGluingObject R C D M)))) (ULift.up (Simplex.vertex X))).edge,
      homotopyIntervalEdge.edge) = _
  have hi : (Truncated.Edge.id (X := (truncation 2).obj
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (dgNerve R (DGGluingObject R C D M)))) (ULift.up (Simplex.vertex X))).edge =
      ULift.up (Truncated.Edge.id (X := (truncation 2).obj
        (dgNerve R (DGGluingObject R C D M))) (Simplex.vertex X)).edge := rfl
  rw [hi]
  change ULift.up (dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
    ((Truncated.Edge.id (X := (truncation 2).obj (dgNerve R (DGGluingObject R C D M)))
      (Simplex.vertex X)).edge.map (dgGluingToComma R C D M))
    (stdSimplex.objEquiv (homotopyIntervalEdge.{max (u + 1) v w}).edge).toOrderHom) = _
  have hb : (stdSimplex.objEquiv
      (homotopyIntervalEdge.{max (u + 1) v w}).edge).toOrderHom = OrderHom.id := by
    ext i
    fin_cases i <;> rfl
  rw [hb, dgCommaNerve_vertex_identity_simplex,
    dgGluingSimplex_unit_map, dgGluingCommaPrism_unitEdge]
  rfl

end SerrePositivity.InfinityCategories
