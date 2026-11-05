module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.CocartesianPathSpace
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.Core.ZeroTargetArrows
public import SerrePositivity.InfinityCategories.Stable.CofiberZeroSource
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberSquareFamily
public import SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExactDiagrams

/-!
分割で生成：docstring を書き直すこと
概要：零終点矢印の元の cofiber 全族を、同じ始点の suspension 全図式と比較する。
方針：元の二つの零角を保持して suspension 図式圏へ入れ、始点評価の fiber で比較する。
規約：比較は始点で恒等。使われ方：一般商の suspension 比較の二次の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
namespace SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily
open SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
  (ha : ∀ x, IsZeroTargetArrow (a.app (Opposite.op ⦋0⦌) x))

include ha in
lemma squareAt_isSuspension (x : A _⦋0⦌) :
    IsSuspensionDiagramVertex ((squares X a).app (Opposite.op ⦋0⦌) x) := by
  refine ⟨squareAt_zero X a x, ?_, squareAt_isPushout X a x⟩
  let s := cofiberSquareAt X a x
  change IsZeroVertex (squareVertex s.square 1 0)
  rw [s.target_vertex]
  have ht := (intervalFunctorVertexTypedEdge (a.app (Opposite.op ⦋0⦌) x)).tgt_eq
  change X.δ 0 (intervalFunctorVertexEdge (a.app (Opposite.op ⦋0⦌) x)) = _ at ht
  change IsZeroVertex (X.δ 0 (intervalFunctorVertexEdge (a.app (Opposite.op ⦋0⦌) x)))
  rw [ht]
  exact ha x

def zeroTargetDiagrams : A ⟶ suspensionDiagrams X :=
  fullSubcomplexLift IsSuspensionDiagramVertex (squares X a) (squareAt_isSuspension X a ha)

def suspensionDiagramsAtSource : A ⟶ suspensionDiagrams X :=
  (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
    SuspensionExact.diagrams X

lemma suspensionDiagramsAtSource_source :
    suspensionDiagramsAtSource X a ≫ suspensionDiagramEvaluation X 0 0 =
      a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [suspensionDiagramsAtSource, Category.assoc, SuspensionExact.diagrams_source,
    Category.comp_id]

end SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.squareAt_isSuspension := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_isSuspension

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.suspensionDiagramsAtSource (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.suspensionDiagramsAtSource := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.suspensionDiagramsAtSource

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.suspensionDiagramsAtSource_source := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.suspensionDiagramsAtSource_source

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroTargetDiagrams (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroTargetDiagrams := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroTargetDiagrams

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.suspensionDiagramsAtSource._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.suspensionDiagramsAtSource._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.suspensionDiagramsAtSource.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.suspensionDiagramsAtSource.eq_1
