module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.Unique
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanFibrationVanishing
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.KanPullbackFibers

/-!
分割で生成：docstring を書き直すこと
概要：K-cof 所有の一般 Kan 引き戻し共終性入力を長完全列から証明する。
方針：右列の fiber の正次数消滅を基点付き fiber 同型で左列へ渡す。
規約：結論は既存の Prop そのもの。元の第一射影の誘導写像を保持する。
使われ方：Sp-8 (3)、K-cof への供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
end SerrePositivity.KST.LocalizingInvariants.CoreFlag
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoreFlag
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag
open _root_.SerrePositivity.KST.Spectra

/-- 厳密引き戻しの fiber の正次数は、右列の消滅から一意となる。 -/
lemma pullback_positive_fiber_subsingleton
    {P X E B : SSet.{u}} [KanComplex P] [KanComplex X] [KanComplex E] [KanComplex B]
    (q : P ⟶ X) (s : P ⟶ E) (g : X ⟶ B) (p : E ⟶ B)
    (h : IsPullback q s g p) [Fibration q] [Fibration p]
    (hE : ∀ n (e : E _⦋0⦌), Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy E n e))
    (hB : ∀ n, 1 < n → ∀ b : B _⦋0⦌, Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy B n b))
    (a : P _⦋0⦌) (n : ℕ) (hn : 0 < n) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber q (q.app _ a)) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint q a)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.fibration_positive_fiber_subsingleton p hE hB (s.app _ a) n hn
  exact Function.Injective.subsingleton
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.pullbackFiberIso h a) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.pullbackFiberIso_point h a)).injective

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoreFlag

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
