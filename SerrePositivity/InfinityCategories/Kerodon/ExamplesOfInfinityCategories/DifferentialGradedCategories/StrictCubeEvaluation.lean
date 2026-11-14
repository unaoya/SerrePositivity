module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardConstantTopEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：strict な順序図式の正次元の立方体成分は零。
方針：既存の旗の和の各項は同じ定数単体の正次数成分。
規約：IS-W2 C05の既存構成の評価則の証明分割。
使われ方：HA 1.3.1.16、strict nerveの二比較の全単体での照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- strict 順序図式の正次元の立方体評価は零。 -/
theorem coherentCubeComponent_orderDiagram_pos {J : Type u} [LinearOrder J]
    (F : J ⥤ ClosedCategory R D) {a b : J} (hab : a < b)
    (S : Finset (Set.Ioo a b)) (hS : 0 < S.card) :
    coherentCubeComponent (enrichedFunctorOfOrderDiagram F) hab S = 0 := by
  unfold coherentCubeComponent cubeEvaluation
  apply Finset.sum_eq_zero
  intro σ _
  have h : cubeFlagEvaluation (σ.trans (descendingEnumeration S))
      (coherentCubeHom (enrichedFunctorOfOrderDiagram F) hab S) = 0 := by
    apply standardTopEval_constant_pos _ _ hS
  rw [h, smul_zero]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
