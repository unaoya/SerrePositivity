module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
分割で生成：docstring を書き直すこと
概要：Ω スペクトルの整数次数のホモトピー群への関手。
方針：標準段での正次数の誘導準同型を使う。
規約：標準段 |j|+1 の計算次数の正値性を明示する。
使われ方：BF 1978 §2、HA §1.4.2。定理 3.1 の π_* 同型の界面。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.OmegaSpectrum
end SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
open _root_.SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき射は基点の頂点表示を保つ。
方針：Under の可換条件を零次単体で評価する。
規約：任意の点つき単体集合の射。
使われ方：BF 1978 §2。整数次数の誘導準同型の基点条件。 -/
theorem pointedMap_basepoint {A B : PointedSimplicialSet.{u}} (f : A ⟶ B) :
    f.right.app _ A.basepoint = B.basepoint :=
  congrArg (fun k : 𝟙_ SSet.{u} ⟶ B.right ↦ k.app _ PUnit.unit) (Under.w f)

end

end SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.OmegaSpectrum.pointedMap_basepoint := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
