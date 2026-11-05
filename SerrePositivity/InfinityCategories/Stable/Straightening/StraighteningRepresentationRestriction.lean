module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransportRepresentation
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexDomains
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertex

/-!
分割で生成：docstring を書き直すこと
 # 元の分類・表現比較を初頂点へ戻し、同じ指定比較を回収する
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Stable.Straightening
open SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))

local instance instLeftFibrationSndSSetTransportSimplexFirstVertexMap : LeftFibration (pullback.snd p (transportSimplexFirstVertexMap B)) :=
  ⟨leftFibrations.pullback_snd p _ (LeftFibration.mem (p := p))⟩

end SerrePositivity.InfinityCategories.Stable.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.instLeftFibrationSndSSetTransportSimplexFirstVertexMap := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.instLeftFibrationSndSSetTransportSimplexFirstVertexMap
