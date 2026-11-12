module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedMaps
public import SerrePositivity.KST.SConstruction.PointedEnrichedKanLift
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityMonoidal

/-! # Ex∞ の標準点つき厳密豊穣 Kan 置換
概要：元の全 basedHom パラメータと基点を保持して、Ex∞ の同じ実 Kan 値へ送る。
方針：有限積保存と monoidal な単位を持つ既存 Ex∞ の全作用を Kan 全部分圏へ束ねる。
規約：元の高次入力を省略しない。使われ方：反復 K 実現の各段と BF の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet


/-- 同じ Ex∞ の実値と元の基点の像を持つ、標準点つき厳密豊穣関手。 -/
def exInfinityPointedEnrichedFunctor :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedSSetObject.{u} :=
  coaugmentedPointedEnrichedFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit

/-- Ex∞ の同じ実 Kan 値を持つ、全 basedHom を保持する厳密豊穣関手。 -/
def exInfinityPointedKanEnrichedFunctor :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedKanObject.{u} :=
  pointedEnrichedKanLift exInfinityPointedEnrichedFunctor
    (fun X => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex X.obj.right)

/-- Kan 置換の点つき実値は、元の基点を Ex∞ の単位で写した同じ対象。 -/
lemma exInfinityPointedKanEnrichedFunctor_obj (X : PointedSSetObject.{u}) :
    (exInfinityPointedKanEnrichedFunctor.obj X).obj =
      Under.mk (X.obj.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app X.obj.right) := rfl

/-- 元の通常の点つき射を、同じ Ex∞ の通常射へ送る実際の Kan 射。 -/
def exInfinityPointedKanMap {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    exInfinityPointedKanEnrichedFunctor.obj X ⟶ exInfinityPointedKanEnrichedFunctor.obj Y :=
  ObjectProperty.homMk
    (show (exInfinityPointedKanEnrichedFunctor.obj X).obj ⟶
      (exInfinityPointedKanEnrichedFunctor.obj Y).obj from
        coaugmentedPointedMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit f)

/-- 全 Hom の作用は、通常射では同じ元の Ex∞ 射を厳密に回収する。 -/
lemma exInfinityPointedKanEnrichedFunctor_hom {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet.{u} f ≫ exInfinityPointedKanEnrichedFunctor.map X Y =
      eHomEquiv SSet.{u} (exInfinityPointedKanMap f) :=
  pointedEnrichedKanLift_hom _ _ f _
    (coaugmentedPointedEnrichedFunctor_hom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit f)

/-- 元の基点を厳密に保つ、同じ Ex∞ 単位の実際の成分。 -/
def exInfinityPointedUnit (X : PointedSSetObject.{u}) :
    X.obj ⟶ (exInfinityPointedKanEnrichedFunctor.obj X).obj :=
  coaugmentedPointedUnit _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit X

/-- 置換への同じ点つき単位の基礎射は anodyne。 -/
lemma exInfinityPointedUnit_anodyne (X : PointedSSetObject.{u}) :
    anodyneExtensions (exInfinityPointedUnit X).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne X.obj.right

/-- Kan Hom への全作用は、包含後に同じ元の全閉 Hom 作用を回収する。 -/
lemma exInfinityPointedKanEnrichedFunctor_inclusion (X Y : PointedSSetObject.{u}) :
    exInfinityPointedKanEnrichedFunctor.map X Y ≫
      PointedObject.basedHomι (exInfinityPointedKanEnrichedFunctor.obj X).obj
        (exInfinityPointedKanEnrichedFunctor.obj Y).obj =
      (coaugmentedPointedInternalFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit).map X Y :=
  (coaugmentedPointedFamilyMap_inclusion _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit X Y).trans (curry_uncurry _)

/-- 同じ Ex∞ 単位は、元の全 basedHom 作用と全パラメータで厳密に可換する。 -/
lemma exInfinityPointedUnit_action (X Y : PointedSSetObject.{u}) :
    ((exInfinityPointedUnit X).right ▷ (X ⟶[SSet.{u}] Y)) ≫
      uncurry (exInfinityPointedKanEnrichedFunctor.map X Y ≫
        PointedObject.basedHomι (exInfinityPointedKanEnrichedFunctor.obj X).obj
          (exInfinityPointedKanEnrichedFunctor.obj Y).obj) =
      uncurry (PointedObject.basedHomι X.obj Y.obj) ≫ (exInfinityPointedUnit Y).right := by
  rw [exInfinityPointedKanEnrichedFunctor_inclusion]
  exact coaugmentedPointedUnit_action _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit X Y

end SerrePositivity.KST.SConstruction
