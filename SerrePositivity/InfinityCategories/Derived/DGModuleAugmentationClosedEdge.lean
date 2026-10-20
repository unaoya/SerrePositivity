module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationActualComponent
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
/-!
概要：実 augmentation ホモトピーの同じ頂点辺を、元の augmentation の持ち上げた実閉辺へ同定する。
方針：同じ閉零成分の一致を辺の全データの一致へ昇格し、実 dg 関手による辺の像を回収する。
規約：ホモトピーの頂点辺を選び直さない。使われ方：同じ空間値 augmentation の可逆性。
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
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
lemma dgModuleAugmentationNerveHomotopy_vertex_edge
    (X : DGModuleFunctorResolutionObject R C E F) :
    (simplicialHomotopyVertexEdge (dgModuleAugmentationNerveHomotopy R C E F)
      (Simplex.vertex X)).edge =
    (dgClosedEdge R (DGUniverseLift.{max (u + 1) w, v} (RightModule R E))
      ((dgUniverseLiftUp.{u, max (u + 1) w, v} R
        (RightModule R E)).onClosed.map X.augmentation)).edge := by
  rw [← dgClosedEdge_map R (RightModule R E)
    (dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E)) X.augmentation]
  apply Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact eq_of_heq (dgModuleAugmentationNerveHomotopy_vertex_edgeHom R C E F X)
end SerrePositivity.InfinityCategories
