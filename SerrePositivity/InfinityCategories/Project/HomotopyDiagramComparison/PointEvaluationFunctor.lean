module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap

/-!
概要：評価点の同型を、全関手空間上の一つの評価関手同型へ送る。
方針：普遍評価を転置し、その同じ単体的射で元の頂点同型を写す。
規約：各関手で独立に同型を選ばず、全パラメータを保持する。
使われ方：Yoneda の恒等点像と反変輸送点の同型を全相対 Hom の評価へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 普遍評価を転置した、元の評価点を動かす実際の単体的関手。 -/
def pointEvaluationFunctor (X Y : SSet.{u}) : X ⟶ (ihom ((ihom X).obj Y)).obj Y :=
  curry ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y)

/-- 転置した同じ普遍評価の頂点は、元の点で評価する同じ関手の頂点。 -/
lemma pointEvaluationFunctor_vertex {X Y : SSet.{u}} (x : X _⦋0⦌) :
    (pointEvaluationFunctor X Y).app (Opposite.op ⦋0⦌) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) x) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro f
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  rfl

/-- 評価点の元の同型は、全関手空間上の元の評価写像の関手同型を与える。 -/
def evaluateFunctorAt_vertexIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {a b : X _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) b) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (pointEvaluationFunctor X Y)
  rw [pointEvaluationFunctor_vertex, pointEvaluationFunctor_vertex] at h
  exact h

/-- 全関手空間の合成を元の点で評価すると、元の第一関手の値で第二の全族を評価する。 -/
lemma functorComposition_evaluate_const {X Y Z K : SSet.{u}}
    (v : ((ihom X).obj Y) _⦋0⦌) (q : K ⟶ (ihom Y).obj Z) (x : X _⦋0⦌) :
    lift (SSet.const v) q ≫ MonoidalClosed.comp X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x =
      q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) x).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y).surjective v
  change lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) q ≫ MonoidalClosed.comp X Y Z ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x = q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) x).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  change (q.app n k).app n (𝟙 n) (f.app n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n.unop.len)) =
    (q.app n k).app n (𝟙 n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (f.app (Opposite.op ⦋0⦌) x) n.unop.len)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
