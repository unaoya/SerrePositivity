module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexEquivalence

/-!
概要：元の coherent 変換の一点パラメーターの図式を、元の指定辺の一点評価へ移す。
方針：元の区間模型の頂点と辺の往復を使い、各次数の評価を直接照合する。
規約：元の辺の全一単体と、元の三角形を保持する。
使われ方：反復射影の合成三角形の評価から元の Kan 合成ホモトピーを回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の変換の一点パラメーターの全図式は、同じ元の辺の prism の表示そのもの。 -/
lemma coherentTransformationFamilyDiagram_const_prism {B : SSet.{u + 1}}
    {F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram (SSet.const t : (Δ[0] : SSet.{u + 1}) ⟶ _) =
      (Δ[1] ◁ fst B (Δ[0] : SSet.{u + 1})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex t) := by
  obtain ⟨e, rfl⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)).surjective t
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) = e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply e
  calc
    _ = (Δ[1] ◁ fst B (Δ[0] : SSet.{u + 1})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism e := by
      apply SSet.hom_ext
      rintro ⟨⟨n⟩⟩
      apply ConcreteCategory.hom_ext
      intro s
      rfl
    _ = _ := congrArg (fun a ↦ (Δ[1] ◁ fst B (Δ[0] : SSet.{u + 1})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism a)
      he.symm

/-- 元の変換図式を元の底の一点で制限すると、元の評価辺を表す区間の射。 -/
lemma coherentTransformationFamilyDiagram_at {B : SSet.{u + 1}}
    {F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌) :
    lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (b, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram (SSet.const t : (Δ[0] : SSet.{u + 1}) ⟶ _) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex t) b).edge := by
  rw [coherentTransformationFamilyDiagram_const_prism, ← Category.assoc]
  have he : lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (b, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})))) ≫
        (Δ[1] ◁ fst B (Δ[0] : SSet.{u + 1})) =
      lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const b) := rfl
  rw [he]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism_const (A := (Δ[1] : SSet.{u + 1}))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex t) b
  have h' := congrArg (fun a ↦ lift (𝟙 (Δ[1] : SSet.{u + 1})) (𝟙 _) ≫ a) h
  simp only [← Category.assoc, lift_fst, Category.id_comp] at h'
  have hd : lift (𝟙 (Δ[1] : SSet.{u + 1})) (𝟙 _) ≫
      (Δ[1] ◁ (SSet.const b : (Δ[1] : SSet.{u + 1}) ⟶ B)) =
        lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const b) := rfl
  rw [hd] at h'
  exact h'

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
