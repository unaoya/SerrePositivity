module


public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
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
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FreeInterval
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMappingNaturality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanAnodyneMappingLifts
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.Spectra.Pointed.Basic
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.Pointed.SmashMonoidal
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：両端を固定しない点つき path space と端点評価。
方針：自由区間からの内部 Hom と anodyne 射による制限を使う。
規約：端点の面添字一が始点、零が終点。基点は定数 path。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。任意の射の fibration 置換。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：anodyne な点つき射による内部 Hom の制限は全ての単射に RLP を持つ。
方針：基礎指数の相対充填を基点条件の等化子へ戻す。
規約：標的の Kan 性だけを要求する。
使われ方：Goerss–Jardine I §7、HTT A.3.3。自由な path の端点評価。 -/
theorem PointedMapping.anodyne_prePointed_rlp {A B : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] : (MorphismProperty.monomorphisms SSet.{u}).rlp
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y).right := by
  intro S T j hj
  let : HasLiftingProperty j ((MonoidalClosed.pre i.right).app Y.right) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyne_pre_rlp_monomorphisms i.right hi Y.right j hj
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_hasLiftingProperty i Y j

/-- 概要：自由な区間を源とする点つき path space。
方針：点つき内部 Hom を使う。
規約：基点以外の path の両端点は自由。
使われ方：Goerss–Jardine I §7、BF 1978 §2。mapping path の全空間。 -/
abbrev freePathSpace (Y : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.basedHom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} Y

/-- 概要：Kan 標的の自由な path space は Kan。
方針：点つき内部 Hom の Kan 性を適用する。
規約：区間の Kan 性は不要。
使われ方：Goerss–Jardine I §7、HTT A.3.3。mapping path の各段。 -/
instance freePathSpace_kanComplex (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 概要：自由な path の端点の評価。
方針：端点包含による制限を単位からの内部 Hom の同型へ合成する。
規約：面添字一が始点、零が終点。
使われ方：Goerss–Jardine I §7。mapping path の二つの射影。 -/
def freePathEndpoint (Y : PointedSimplicialSet.{u}) (i : Fin 2) : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y ⟶ Y :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} i) Y ≫
    (MonoidalClosed.unitIsoSelf (X := Y)).hom

/-- 概要：各端点への評価は全ての単射に対して RLP を持つ。
方針：端点包含の anodyne 性と単位の同型の合成を使う。
規約：モデル構造の弱同値は使わない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。mapping path の射影の π_* 同型。 -/
theorem freePathEndpoint_rlp (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (i : Fin 2) : (MorphismProperty.monomorphisms SSet.{u}).rlp
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y i).right := by
  let e := PointedSimplicialSet.forget.mapIso (MonoidalClosed.unitIsoSelf (X := Y))
  exact (MorphismProperty.monomorphisms SSet.{u}).rlp.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint_anodyne i) Y)
    ((MorphismProperty.monomorphisms SSet.{u}).rlp_of_isIso e.hom)

/-- 概要：自由な path の端点への評価は Kan fibration。
方針：単射への RLP をホーン包含へ制限する。
規約：両端点に共通。
使われ方：Goerss–Jardine I §7、HTT A.3.3。mapping path の Kan 性。 -/
instance freePathEndpoint_fibration (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (i : Fin 2) : Fibration (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y i).right :=
  (fibration_iff _).2 (fun _ _ j hj ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint_rlp Y i j (J_le_monomorphisms _ hj))

/-- 概要：自由な path space への定数 path の射。
方針：区間の潰す射で内部 Hom の源を制限する。
規約：点つき射として定義する。
使われ方：Goerss–Jardine I §7。mapping path の比較射。 -/
def freeConstantPath (Y : PointedSimplicialSet.{u}) : Y ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y :=
  (MonoidalClosed.unitIsoSelf (X := Y)).inv ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse.{u} Y

/-- 概要：定数 path のどちらの端点も元の点。
方針：制限の反変関手性と端点を潰した恒等式を使う。
規約：点つき射の等式。
使われ方：Goerss–Jardine I §7。mapping path の厳密な因子分解。 -/
@[reassoc (attr := simp)]
theorem freeConstantPath_endpoint (Y : PointedSimplicialSet.{u}) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath Y ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y i = 𝟙 Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    Category.assoc]
  have h : (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse.{u}).app Y ≫
      (MonoidalClosed.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} i)).app Y = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint_collapse,
      MonoidalClosed.pre_id]
    rfl
  change (MonoidalClosed.unitIsoSelf (X := Y)).inv ≫
    ((MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse.{u}).app Y ≫
      (MonoidalClosed.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} i)).app Y) ≫
        (MonoidalClosed.unitIsoSelf (X := Y)).hom = _
  rw [h, Category.id_comp, Iso.inv_hom_id]

end

end SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
