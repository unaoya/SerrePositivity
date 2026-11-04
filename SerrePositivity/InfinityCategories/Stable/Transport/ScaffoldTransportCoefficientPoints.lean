module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacement
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementFiber
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftCoherentTransportReconstruction
public import SerrePositivity.InfinityCategories.F1.Scaffold.TautScaffold
public import SerrePositivity.InfinityCategories.F1.Scaffold.UniversalScaffold
public import SerrePositivity.InfinityCategories.F1.Scaffold.UniversalScaffoldFiber
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransport
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransportEvaluation
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransportWeightedNerve
public import SerrePositivity.InfinityCategories.F1.Weighted.Nerve
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveFiber
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportCoefficientFiber
public import SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan
public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan

/-!
分割で生成：docstring を書き直すこと
 # 同じ相対三角の係数 fiber 点は、元の恒等射評価と weighted 包含を回収する
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
namespace ScaffoldTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : ScaffoldTransportComparisonSpan p)

/-- 元の係数値上の source 脚は、元の恒等射評価そのもの。 -/
theorem coefficientEmbedding_source (c : I) :
    s.coefficientEmbedding c ≫ s.toStrictTransportComparisonSpan.coherentSource =
      (SSet.uliftFunctor.{u + 1, u}).map
        (leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)) := by
  rw [coefficientEmbedding, StrictTransportComparisonSpan.coherentSource,
    ← Functor.map_comp, Category.assoc, s.source_restriction,
    simplicialReplacementConstantLift_universalScaffold]

/-- 元の係数値上の weighted 脚は、同じ定値包含と同じ coherent 比較を通る。 -/
theorem coefficientEmbedding_target (c : I) :
    s.coefficientEmbedding c ≫ s.toStrictTransportComparisonSpan.coherentTarget =
      (SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveConstantLift (leftStrictTransportDiagram p) c) ≫
          leftCoherentTransportComparison p := by
  rw [coefficientEmbedding, StrictTransportComparisonSpan.coherentTarget,
    ← Category.assoc, ← Functor.map_comp, Category.assoc, s.weighted_restriction,
    simplicialReplacementConstantLift_tautScaffold]

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration
