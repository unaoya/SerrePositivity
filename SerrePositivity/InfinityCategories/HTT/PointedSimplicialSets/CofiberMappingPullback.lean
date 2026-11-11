module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMappingNaturality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.Spectra.Pointed.AdjoinBasepoint
public import SerrePositivity.Spectra.Pointed.Basic
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.Pointed.SmashMonoidal
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
分割で生成：docstring を書き直すこと
概要：点つき cofiber からの写像空間を与える引き戻し。
方針：内部 Hom の源に関する反変関手が極限を保つことを使う。
規約：通常の単体集合の厳密な pullback の主張。
使われ方：Goerss–Jardine I §7、HTT A.3.3。loop と path fiber の比較。
-/

@[expose] public section

universe v w u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance instIsRightAdjointSSetPointedSimplicialSetForget : PointedSimplicialSet.forget.{u}.IsRightAdjoint :=
  PointedObject.adjoinForgetAdjunction.isRightAdjoint

/-- 概要：標的を固定した点つき内部 Hom の基礎単体集合の反変関手。
方針：閉構造の反変 Hom と基点忘却を合成する。
規約：始域は点つき単体集合の反対圏。
使われ方：HTT A.3.3、Goerss–Jardine I §7。cofiber の Hom の pullback。 -/
def cofiberMappingFunctor (Z : PointedSimplicialSet.{u}) :
    PointedSimplicialSet.{u}ᵒᵖ ⥤ SSet.{u} :=
  MonoidalClosed.internalHom.flip.obj Z ⋙ PointedSimplicialSet.forget

/-- 概要：反変写像空間関手は極限を保つ。
方針：閉構造のパラメータ付き随伴と忘却の右随伴性を合成する。
規約：任意の添字圏 J。
使われ方：HTT A.3.3。cofiber の pushout を Hom の pullback へ移す。 -/
instance cofiberMappingFunctor_preservesLimitsOfShape (Z : PointedSimplicialSet.{u})
    (J : Type v) [Category.{w} J] : PreservesLimitsOfShape J (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Z) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor]
  infer_instance

/-- 概要：反変写像空間関手の射の作用は既存の源の制限。
方針：閉構造の pre と等化子による制限の一致を使う。
規約：任意の点つき射 i。
使われ方：Goerss–Jardine I §7。pullback の各辺の計算。 -/
@[simp]
theorem cofiberMappingFunctor_map (Z : PointedSimplicialSet.{u})
    {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Z).map i.op = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z := by
  change ((MonoidalClosed.pre i).app Z).right = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  rfl

end

end SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.cofiberMappingFunctor := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.cofiberMappingFunctor_map := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_map

@[deprecated _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_preservesLimitsOfShape (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.cofiberMappingFunctor_preservesLimitsOfShape := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_preservesLimitsOfShape

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.instIsRightAdjointSSetPointedSimplicialSetForget := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.instIsRightAdjointSSetPointedSimplicialSetForget

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.cofiberMappingFunctor._proof_1 := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.cofiberMappingFunctor._proof_2 := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor._proof_2
