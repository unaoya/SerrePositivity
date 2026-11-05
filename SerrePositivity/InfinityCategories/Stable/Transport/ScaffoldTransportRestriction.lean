module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan
namespace SerrePositivity.InfinityCategories.Stable.Transport
open SerrePositivity.KST.Fibration
namespace ScaffoldTransportComparisonSpan
open SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan p)

/-- 元の scaffold の同じ埋め込みを宇宙持ち上げする。 -/
def coherentEmbedding :
    (SSet.uliftFunctor.{u + 1, u}).obj (simplicialReplacement (leftStrictTransportDiagram p)) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj s.total :=
  (SSet.uliftFunctor.{u + 1, u}).map s.embedding

/-- 元の scaffold 上への source 脚の厳密な制限。 -/
theorem coherentEmbedding_source :
    (coherentEmbedding s) ≫ s.toStrictTransportComparisonSpan.coherentSource =
      (SSet.uliftFunctor.{u + 1, u}).map (universalScaffold p) := by
  rw [coherentEmbedding, StrictTransportComparisonSpan.coherentSource,
    ← Functor.map_comp, s.source_restriction]

/-- weighted 比較への因子分解も、元の taut scaffold 上で厳密に回収する。 -/
theorem coherentEmbedding_target :
    (coherentEmbedding s) ≫ s.toStrictTransportComparisonSpan.coherentTarget =
      (SSet.uliftFunctor.{u + 1, u}).map (tautScaffold (leftStrictTransportDiagram p)) ≫
        leftCoherentTransportComparison p := by
  rw [coherentEmbedding, StrictTransportComparisonSpan.coherentTarget,
    ← Category.assoc, ← Functor.map_comp, s.weighted_restriction]

end ScaffoldTransportComparisonSpan
end SerrePositivity.InfinityCategories.Stable.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coherentEmbedding (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coherentEmbedding := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coherentEmbedding

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coherentEmbedding_source := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coherentEmbedding_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coherentEmbedding_target := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coherentEmbedding_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coherentEmbedding.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coherentEmbedding.eq_1
