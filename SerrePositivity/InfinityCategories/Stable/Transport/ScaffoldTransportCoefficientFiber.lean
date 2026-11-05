module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacement
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementFiber
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftCoherentTransportReconstruction
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverPrecomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransport
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransportWeightedNerve
public import SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan
public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan

/-!
分割で生成：docstring を書き直すこと
 # 元の係数点の三角を、底を固定した同じ unstraightening fiber 内で比較する
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

/-- 元の係数値から、同じ scaffold の埋め込みを通って共通全空間に入る。 -/
def coefficientEmbedding (c : I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (leftStrictTransport p c) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj s.total :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (simplicialReplacementConstantLift (leftStrictTransportDiagram p) c ≫ s.embedding)

/-- 元の係数値の底を、宇宙と始域を固定して表示する。 -/
def coefficientBase (c : I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (leftStrictTransport p c) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) :=
  SSet.const (ULift.up (nerveVertex c))

/-- 同じ係数値上では共通底は元の指定頂点に厳密に定値。 -/
theorem coefficientEmbedding_over (c : I) :
    (coefficientEmbedding s) c ≫ s.toStrictTransportComparisonSpan.coherentBase =
      coefficientBase (p := p) c := by
  rw [coefficientEmbedding, _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan.coherentBase,
    ← Functor.map_comp, Category.assoc, s.embedding_over,
    simplicialReplacementConstantLift_projection]
  rfl

/-- 相対三角を係数値に制限し、その指定点で評価する同じ fiber への写像。 -/
def coefficientRelativeEvaluation (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    relativeFunctorSpace (leftUnstraighteningProjection (leftCoherentTransport p))
      s.toStrictTransportComparisonSpan.coherentBase ⟶
        vertexFiber (leftUnstraighteningProjection (leftCoherentTransport p))
          (ULift.up (nerveVertex c)) :=
  relativeFunctorOverPre (leftUnstraighteningProjection (leftCoherentTransport p))
    (Over.homMk (U := Over.mk (coefficientBase (p := p) c))
      (V := Over.mk s.toStrictTransportComparisonSpan.coherentBase)
      ((coefficientEmbedding s) c) ((coefficientEmbedding_over s) c)) ≫
    relativeFunctorEvaluate (leftUnstraighteningProjection (leftCoherentTransport p))
      (coefficientBase (p := p) c) (ULift.up v)

end ScaffoldTransportComparisonSpan
end SerrePositivity.InfinityCategories.Stable.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientBase (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientBase := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientBase

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientEmbedding := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientEmbedding_over := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding_over

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientRelativeEvaluation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientRelativeEvaluation := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientRelativeEvaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientEmbedding.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientEmbedding.eq_1
