module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
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
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorTerminal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorInitial
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroDiagramComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily

/-!
分割で生成：docstring を書き直すこと
概要：元の cofiber 四角形の全族は関手圏内の零角四角形である。
方針：全族の転置と頂点評価の比較で零角を同定し、h Fun の合成の零性を得る。
規約：点ごとの零合成ではない。使われ方：差の実随伴単位の四辺の可換性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 零頂点の存在は、任意のパラメータの関手圏へ移る。 -/
lemma functorHasZeroVertex (A X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex ((ihom A).obj X) := by
  let z : A ⟶ X := SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).vertex
  have hz : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (z.app (Opposite.op ⦋0⦌) a) := by
    intro a
    rw [show z = SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).vertex from rfl, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).isZero
  exact ⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_functorVertex_of_pointwise z (fun a => (hz a).1),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise z (fun a => (hz a).2)⟩⟩

namespace CofiberFamily
open _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

/-- 元の普遍四角形の左上の零角を与える全関手。 -/
def zeroCorner : A ⟶ X := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares X a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
  (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma zeroCorner_zero (x : A _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberFamily.zeroCorner X a).app (Opposite.op ⦋0⦌) x) := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squareAt X a x) = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares X a).app (Opposite.op ⦋0⦌) x :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _).app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares X a).app _ x))
  rw [← hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squareAt_zero X a x

local instance cofiberFamilyFunctorZero : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex ((ihom A).obj X) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.functorHasZeroVertex A X

end CofiberFamily
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.functorHasZeroVertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.functorHasZeroVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.cofiberFamilyFunctorZero := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberFamily.cofiberFamilyFunctorZero

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberFamily.zeroCorner (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroCorner := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberFamily.zeroCorner

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroCorner_zero := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberFamily.zeroCorner_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroCorner._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberFamily.zeroCorner._proof_1
