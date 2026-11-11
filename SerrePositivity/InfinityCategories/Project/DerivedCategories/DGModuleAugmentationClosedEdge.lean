module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationActualComponent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
lemma dgModuleAugmentationNerveHomotopy_vertex_edge
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy R C E F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).edge =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) w, v} (RightModule R E))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R
        (_root_.SerrePositivity.DifferentialGraded.RightModule R E)).onClosed.map X.augmentation)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map R (RightModule R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E)) X.augmentation]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy_vertex_edgeHom R C E F X)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
