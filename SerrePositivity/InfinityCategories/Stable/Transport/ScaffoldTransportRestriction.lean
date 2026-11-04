module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacement
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftCoherentTransportReconstruction
public import SerrePositivity.InfinityCategories.F1.Scaffold.TautScaffold
public import SerrePositivity.InfinityCategories.F1.Scaffold.UniversalScaffold
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransportWeightedNerve
public import SerrePositivity.InfinityCategories.F1.Weighted.Nerve
public import SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan
public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan

/-!
分割で生成：docstring を書き直すこと
 # 元の scaffold に制限した、同じ coherent transport の相対三角
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

/-- 元の scaffold の同じ埋め込みを宇宙持ち上げする。 -/
def coherentEmbedding :
    (SSet.uliftFunctor.{u + 1, u}).obj (simplicialReplacement (leftStrictTransportDiagram p)) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj s.total :=
  (SSet.uliftFunctor.{u + 1, u}).map s.embedding

/-- 元の scaffold 上への source 脚の厳密な制限。 -/
theorem coherentEmbedding_source :
    s.coherentEmbedding ≫ s.toStrictTransportComparisonSpan.coherentSource =
      (SSet.uliftFunctor.{u + 1, u}).map (universalScaffold p) := by
  rw [coherentEmbedding, StrictTransportComparisonSpan.coherentSource,
    ← Functor.map_comp, s.source_restriction]

/-- weighted 比較への因子分解も、元の taut scaffold 上で厳密に回収する。 -/
theorem coherentEmbedding_target :
    s.coherentEmbedding ≫ s.toStrictTransportComparisonSpan.coherentTarget =
      (SSet.uliftFunctor.{u + 1, u}).map (tautScaffold (leftStrictTransportDiagram p)) ≫
        leftCoherentTransportComparison p := by
  rw [coherentEmbedding, StrictTransportComparisonSpan.coherentTarget,
    ← Category.assoc, ← Functor.map_comp, s.weighted_restriction]

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration
