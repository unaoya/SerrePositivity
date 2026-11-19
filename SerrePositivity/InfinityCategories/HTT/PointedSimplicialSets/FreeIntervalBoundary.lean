module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.CofiberMappingPullback
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FreeInterval
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMappingNaturality
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedInterval
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.Spectra.Pointed.Basic
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.Pointed.SmashMonoidal
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepoint
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointUnit
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：自由な区間の境界とその点つき写像空間。
方針：二つの頂点の余積に基点を加え、反変内部 Hom の極限保存を使う。
規約：境界の第一成分が終点、第二成分が始点。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。両端点の同時評価。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance instIsLeftAdjointSSetPointedSimplicialSetAdjoinBasepointFunctor : PointedSimplicialSet.adjoinBasepointFunctor.{u}.IsLeftAdjoint :=
  PointedSimplicialSet.adjoinBasepointAdjunction.isLeftAdjoint

/-- 概要：自由な基点を加えた区間の二つの端点。
方針：終単体集合の二項余積に自由な基点を加える。
規約：smash の単位二つの点つき余積となる。
使われ方：Goerss–Jardine I §7。両端点の同時指定の源。 -/
def freeIntervalBoundary : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.adjoinBasepoint ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))

/-- 概要：自由な境界の終点成分。
方針：第一の余積包含に基点を加える。
規約：面添字零の端点に対応する。
使われ方：Goerss–Jardine I §7。境界上の終点評価。 -/
def freeBoundaryEnd : 𝟙_ PointedSimplicialSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} :=
  PointedSimplicialSet.adjoinBasepointFunctor.{u}.map (coprod.inl : 𝟙_ SSet.{u} ⟶ _)

/-- 概要：自由な境界の始点成分。
方針：第二の余積包含に基点を加える。
規約：面添字一の端点に対応する。
使われ方：Goerss–Jardine I §7。境界上の始点評価。 -/
def freeBoundaryStart : 𝟙_ PointedSimplicialSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} :=
  PointedSimplicialSet.adjoinBasepointFunctor.{u}.map (coprod.inr : 𝟙_ SSet.{u} ⟶ _)

/-- 概要：自由な境界から自由な区間への包含。
方針：二つの端点の基礎射に自由な基点を加える。
規約：両端点を同時に含める射。
使われ方：Goerss–Jardine I §7、HTT A.3.3。両端点評価の fibration 性。 -/
def freeBoundaryInclusion : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} :=
  PointedSimplicialSet.adjoinBasepointFunctor.{u}.map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right

/-- 概要：自由な境界の包含は基礎単体集合で単射。
方針：二端点の単射性と基点追加による単射の保存を使う。
規約：HT-KQ を使わない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。境界への内部 Hom の制限。 -/
instance freeBoundaryInclusion_mono : Mono _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u}.right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.mono_coprod_map_id _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right

/-- 概要：境界の終点から区間へ進むと自由な終点包含。
方針：零次面の定数射表示を基点追加へ移す。
規約：面添字零。
使われ方：Goerss–Jardine I §7。終点の評価の同定。 -/
@[reassoc (attr := simp)]
theorem freeBoundaryEnd_inclusion : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u} ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint 0 := by
  have h : PointedSimplicialSet.deltaZeroUnitIso.inv ≫ stdSimplex.δ.{u} (0 : Fin 2) =
      SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm 1) := by
    rw [stdSimplex.δ_zero_eq_const, SSet.comp_const]
  change PointedSimplicialSet.adjoinBasepointFunctor.{u}.map coprod.inl ≫
    PointedSimplicialSet.adjoinBasepointFunctor.{u}.map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right = _
  rw [← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl]
  change _ = PointedSimplicialSet.adjoinBasepointFunctor.{u}.map
    PointedSimplicialSet.deltaZeroUnitIso.{u}.inv ≫
      PointedSimplicialSet.adjoinBasepointFunctor.{u}.map (stdSimplex.δ.{u} (0 : Fin 2))
  rw [← Functor.map_comp, h]

/-- 概要：境界の始点から区間へ進むと自由な始点包含。
方針：一次面の定数射表示を基点追加へ移す。
規約：面添字一。
使われ方：Goerss–Jardine I §7。始点の評価の同定。 -/
@[reassoc (attr := simp)]
theorem freeBoundaryStart_inclusion : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart.{u} ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint 1 := by
  have h : PointedSimplicialSet.deltaZeroUnitIso.inv ≫ stdSimplex.δ.{u} (1 : Fin 2) =
      SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm 0) := by
    rw [stdSimplex.δ_one_eq_const, SSet.comp_const]
  change PointedSimplicialSet.adjoinBasepointFunctor.{u}.map coprod.inr ≫
    PointedSimplicialSet.adjoinBasepointFunctor.{u}.map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right = _
  rw [← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr]
  change _ = PointedSimplicialSet.adjoinBasepointFunctor.{u}.map
    PointedSimplicialSet.deltaZeroUnitIso.{u}.inv ≫
      PointedSimplicialSet.adjoinBasepointFunctor.{u}.map (stdSimplex.δ.{u} (1 : Fin 2))
  rw [← Functor.map_comp, h]

/-- 概要：自由な境界は二つの点つき単位の余積。
方針：基点追加が左随伴として二項余積を保存することを使う。
規約：基礎単体集合の余積ではなく点つき圏の余積。
使われ方：HTT A.3.3、Goerss–Jardine I §7。境界からの Hom の積表示。 -/
def freeBoundaryIsColimit :
    IsColimit (BinaryCofan.mk _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u} _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart) :=
  isColimitOfHasBinaryCoproductOfPreservesColimit
    PointedSimplicialSet.adjoinBasepointFunctor (𝟙_ SSet.{u}) (𝟙_ SSet.{u})

/-- 概要：自由な境界からの写像空間は二つの単位からの写像空間の積。
方針：反変写像空間関手が極限を保つことを余積の反対に適用する。
規約：基礎単体集合の積の普遍性を述べる。
使われ方：HTT A.3.3、Goerss–Jardine I §7。両端点評価の相対充填。 -/
def freeBoundaryHomIsLimit (Y : PointedSimplicialSet.{u}) :
    IsLimit (BinaryFan.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u} Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart.{u} Y)) := by
  have h := mapIsLimitOfPreservesOfIsLimit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Y) _ _
    (BinaryCofan.IsColimit.op _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryIsColimit.{u})
  change IsLimit (BinaryFan.mk ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Y).map _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u}.op)
    ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Y).map _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart.{u}.op)) at h
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_map, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_map] at h
  exact h

/-- 概要：点つき内部 Hom の源の制限は合成を逆順に保つ。
方針：閉構造の pre との一致とその反変関手性を使う。
規約：点つき射の厳密な等式。
使われ方：HTT A.3.3、BF 1978 §2。境界の成分評価。 -/
theorem PointedMapping.prePointed_comp {A B C : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (j : B ⟶ C) (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j Y ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (i ≫ j) Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map]

/-- 概要：自由な境界上の終点を評価する点つき射。
方針：終点成分へ制限して単位の内部 Hom を評価する。
規約：面添字零の端点。
使われ方：Goerss–Jardine I §7。両端点写像空間の積の第一射影。 -/
def freeBoundaryHomEnd (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHom _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} Y ⟶ Y :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u} Y ≫ (unitIsoSelf (X := Y)).hom

/-- 概要：自由な境界上の始点を評価する点つき射。
方針：始点成分へ制限して単位の内部 Hom を評価する。
規約：面添字一の端点。
使われ方：Goerss–Jardine I §7。両端点写像空間の積の第二射影。 -/
def freeBoundaryHomStart (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHom _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} Y ⟶ Y :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart.{u} Y ≫ (unitIsoSelf (X := Y)).hom

/-- 概要：自由な境界からの写像空間は標的二つの積。
方針：単位からの内部 Hom の同型を二つの射影へ合成する。
規約：基礎単体集合の積。
使われ方：HTT A.3.3、Goerss–Jardine I §7。両端点の同時評価。 -/
def freeBoundaryEvaluationIsLimit (Y : PointedSimplicialSet.{u}) :
    IsLimit (BinaryFan.mk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Y).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Y).right) := by
  let e := PointedSimplicialSet.forget.mapIso (unitIsoSelf (X := Y))
  exact BinaryFan.isLimitCompRightIso _ e.hom
    (BinaryFan.isLimitCompLeftIso _ e.hom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomIsLimit Y))

/-- 概要：自由な境界からの写像空間と標的の二項積との標準同型。
方針：二つの積の普遍性を比較する。
規約：第一成分が終点、第二成分が始点。
使われ方：HTT A.3.3、BF 1978 §2。境界制限の fibration を積へ移す。 -/
def freeBoundaryEvaluationIso (Y : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} Y).right ≅ Y.right ⨯ Y.right :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIsLimit Y).conePointUniqueUpToIso
    (t := BinaryFan.mk (prod.fst : Y.right ⨯ Y.right ⟶ Y.right) prod.snd)
    (prodIsProd Y.right Y.right)

/-- 概要：境界評価の標準同型の第一射影は終点評価。
方針：極限の標準比較同型の成分計算を使う。
規約：第一成分が終点。
使われ方：Goerss–Jardine I §7。mapping path の終点射影。 -/
@[reassoc (attr := simp)]
theorem freeBoundaryEvaluationIso_fst (Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).hom ≫ prod.fst = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Y).right :=
  IsLimit.conePointUniqueUpToIso_hom_comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIsLimit Y)
    (prodIsProd Y.right Y.right) ⟨WalkingPair.left⟩

/-- 概要：境界評価の標準同型の第二射影は始点評価。
方針：極限の標準比較同型の成分計算を使う。
規約：第二成分が始点。
使われ方：Goerss–Jardine I §7。mapping path の始点射影。 -/
@[reassoc (attr := simp)]
theorem freeBoundaryEvaluationIso_snd (Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).hom ≫ prod.snd = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Y).right :=
  IsLimit.conePointUniqueUpToIso_hom_comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIsLimit Y)
    (prodIsProd Y.right Y.right) ⟨WalkingPair.right⟩

/-- 概要：自由な path の両端点を同時に評価する射。
方針：境界への制限と境界写像空間の積表示を合成する。
規約：第一射影が終点、第二射影が始点。
使われ方：BF 1978 §2、Goerss–Jardine I §7。mapping path の fibration 性。 -/
def freePathEndpoints (Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right ⟶ Y.right ⨯ Y.right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} Y ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).hom

/-- 概要：自由な path の両端点の同時評価は Kan fibration。
方針：単射な境界への制限の fibration と積表示の同型を合成する。
規約：HT-KQ は不要。
使われ方：BF 1978 §2、HTT A.3.3。任意の射の fibration 置換。 -/
instance freePathEndpoints_fibration (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    Fibration (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints Y) := by
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} Y) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} Y
  unfold _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints
  infer_instance

/-- 概要：両端点の同時評価の第一射影は自由な path の終点評価。
方針：源の制限の合成と境界の終点包含を計算する。
規約：面添字零。
使われ方：BF 1978 §2。mapping path の終点写像。 -/
@[reassoc (attr := simp)]
theorem freePathEndpoints_fst (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints Y ≫ prod.fst = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0).right := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_fst]
  have h : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} Y ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Y =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0 := by
    unfold _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd_inclusion]
  exact congrArg Under.Hom.right h

/-- 概要：両端点の同時評価の第二射影は自由な path の始点評価。
方針：源の制限の合成と境界の始点包含を計算する。
規約：面添字一。
使われ方：BF 1978 §2。mapping path の始点写像。 -/
@[reassoc (attr := simp)]
theorem freePathEndpoints_snd (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints Y ≫ prod.snd = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_snd]
  have h : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} Y ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Y =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1 := by
    unfold _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart_inclusion]
  exact congrArg Under.Hom.right h

end

end SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
