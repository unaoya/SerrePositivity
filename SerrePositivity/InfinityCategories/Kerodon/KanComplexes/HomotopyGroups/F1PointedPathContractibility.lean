module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
分割で生成：docstring を書き直すこと
概要：基点に始まる path space のホモトピー群の自明性。
方針：区間の収縮から基点固定ホモトピーを作り、ホモトピー不変性を適用する。
規約：定数 path を基点とし零次数も扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の次数移動の長完全列。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：基点を経由する定数射は選んだ基点への SSet.const と一致する。
方針：終対象からの射と頂点の同値を使う。
規約：始域 A は任意。
使われ方：Goerss–Jardine I §7。収縮の相対ホモトピー表示。 -/
theorem pointedConstant_eq_const (X : PointedSimplicialSet.{u}) (A : SSet.{u}) :
    toUnit A ≫ X.hom = SSet.const X.basepoint := by
  have h : SSet.const (X := 𝟙_ SSet.{u}) X.basepoint = X.hom :=
    (SSet.unitHomEquiv X.right).symm_apply_apply X.hom
  rw [← h, SSet.comp_const]

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
