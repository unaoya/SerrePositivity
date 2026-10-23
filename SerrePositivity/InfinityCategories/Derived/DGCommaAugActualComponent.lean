module
public import SerrePositivity.InfinityCategories.DGNerve.VertexIdentity
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismComponent
public import SerrePositivity.InfinityCategories.DGNerve.EdgeHomotopy
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
/-!
概要：実 augmentation ホモトピーの同じ頂点成分を、元の augmentation の閉零成分へ同定する。
方針：実恒等辺を単位単体に戻し、実 prism の同じ単位入力辺の係数を評価する。
規約：ホモトピー自身の実辺を保つ。使われ方：実 augmentation の空間値像の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- 実ホモトピーの同じ頂点辺の係数は、元の同じ augmentation。 -/
lemma dgCommaAugmentationNerveHomotopy_vertex_edgeHom
    (X : DGFunctorCommaObject R C E F) :
    HEq ((simplicialHomotopyVertexEdge (dgCommaAugmentationNerveHomotopy R C E F)
      (Simplex.vertex X)).edge.edgeHom 0 1 (by decide))
      (dgCommaAugmentationComponent R C E F X).val := by
  change HEq (((dgCommaAugmentationNervePrism R C E F).app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj
      (dgNerve R (DGFunctorCommaObject R C E F))) (Simplex.vertex X)).edge,
      homotopyIntervalEdge.edge)).edgeHom 0 1 (by decide)) _
  rw [dgNerve_vertex_identity_simplex]
  have hi : (homotopyIntervalEdge.{max u (max v w)}).edge =
      SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u (max v w)})) := by
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  rw [hi]
  exact dgCommaAugmentationNervePrism_unitEdge R C E F X
/-- 同じ実頂点辺の閉零成分そのものも、元の augmentation の閉零成分に等しい。 -/
lemma dgCommaAugmentationNerveHomotopy_vertex_cycle
    (X : DGFunctorCommaObject R C E F) :
    HomotopyComparison.edgeCycle
      (simplicialHomotopyVertexEdge (dgCommaAugmentationNerveHomotopy R C E F)
        (Simplex.vertex X)).toTruncated = dgCommaAugmentationComponent R C E F X := by
  apply Subtype.ext
  apply eq_of_heq
  exact (HomotopyComparison.edgeCycle_val_heq _).trans
    (dgCommaAugmentationNerveHomotopy_vertex_edgeHom R C E F X)
end SerrePositivity.InfinityCategories
