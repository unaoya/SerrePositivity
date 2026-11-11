module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafCoconeVertexEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FlippedConeEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction

/-!
概要：元の指定前層余錐の二変数評価を交換し、元の全評価余錐の coherent な族を回収する。
方針：同じ元の全余錐を交換し、底制限・頂点評価・各全余錐を厳密に照合する。
規約：元の余錐・底図式・実際の頂点関手を保持する。
使われ方：元の有限錐の脚を前層余極限頂点で写したものと、評価余錐の全脚の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 余錐の形状の右の指定頂点。 -/
def coconeRightApexVertex (K : SSet.{u}) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0]))

/-- 元の全余錐を右頂点で評価すると、同じ元の余錐頂点になる。 -/
lemma cocone_vertex_at_rightApex {K X : SSet.{u}} {r : K ⟶ X} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) :
    q.val.app (Opposite.op ⦋0⦌) (coconeRightApexVertex K) = q.vertex := rfl

variable {B C : SSet.{u}}
  {r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)

/-- 元の指定前層余錐の交換評価による、元の全評価余錐の族。 -/
def presheafCoconeFlip : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj B) (Δ[0] : SSet.{u + 1}))).obj
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv _ _ _ q.val

/-- 元の交換全余錐族の底への制限は、元の同じ前層図式の交換評価そのもの。 -/
lemma presheafCoconeFlip_restriction :
    presheafCoconeFlip q ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[0])).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv _ _ _ r := by
  rw [presheafCoconeFlip, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre, q.property]

/-- 元の交換全余錐族の右頂点評価は、元の指定余錐の実際の頂点関手。 -/
lemma presheafCoconeFlip_apex :
    presheafCoconeFlip q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (coconeRightApexVertex ((SSet.uliftFunctor.{u + 1, u}).obj B)) =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeVertexFunctor q := by
  rw [presheafCoconeFlip, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.flippedDiagram_evaluation, cocone_vertex_at_rightApex]
  rfl

/-- 元の交換全余錐族の各点は、元の指定余錐をその点で評価した全余錐そのもの。 -/
lemma presheafCoconeFlip_vertex
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌) :
    (presheafCoconeFlip q).app (Opposite.op ⦋0⦌) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x) q).val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero q.val x

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
