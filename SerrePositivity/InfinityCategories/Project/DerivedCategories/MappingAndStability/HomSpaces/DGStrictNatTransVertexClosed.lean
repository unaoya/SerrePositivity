module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.EdgeHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransVertex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStrictNatTrans
/-!
概要：同じ実ホモトピーの頂点辺を回収し、全関手射の可逆性へ接続する。
方針：元の閉射・実出力分解・関手空間の点ごとの判定を使う。
規約：出力の射影性と始域の Small 性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded

open scoped _root_.Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgStrictNatTrans_homotopy_vertex_cycle
    (A : Type u) [CommRing A] (C E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A C] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
    {F G : DGFunctor A C E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge η.homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)).toTruncated =
      η.app x := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge η.homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)).toTruncated =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (x := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
        (y := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (η.app x)) := by
    apply Truncated.Edge.ext
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_homotopy_vertex_edge η x
  rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle_edgeOfCycle]
lemma dgModuleStrictNatTrans_homotopy_vertex_closed
    (A : Type u) [CommRing A] (C : Type (max (u + 1) v)) (E : Type v)
    [_root_.SerrePositivity.DifferentialGraded.DGCategory A C] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
    {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A C (_root_.SerrePositivity.DifferentialGraded.RightModule A E)}
    (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj x) ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (G.obj x))
    (ha : ∀ x y, F.map x y ≫ _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose A E _ _ _ (a y) =
      G.map x y ≫ _root_.SerrePositivity.DifferentialGraded.moduleHomPrecompose A E _ _ _ (a x)) (x : C) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality A E a ha).homotopy
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)).toTruncated = a x := by
  apply (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A E) _ _).injective
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle, dgStrictNatTrans_homotopy_vertex_cycle]
  rfl
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
