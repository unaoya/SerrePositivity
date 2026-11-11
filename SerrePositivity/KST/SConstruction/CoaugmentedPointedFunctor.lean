module
public import SerrePositivity.KST.SConstruction.CoaugmentedClosedEvaluation
public import SerrePositivity.KST.SConstruction.PointedEnrichedActionFunctor
public import SerrePositivity.KST.Spectra.PointedMappingParameters

/-! # monoidal な単位を持つ関手の標準点つき豊穣作用
概要：元の基点と全 basedHom 族を、単位の像の基点を持つ同じ実値へ送る。
方針：閉 Hom の全作用を使い、単位の全族自然性から厳密な基点保存を示す。
規約：Kan 性はまだ仮定しない。使われ方：Ex∞ の標準点つき厳密豊穣関手。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open Spectra
variable (F : SSet.{u} ⥤ SSet.{u}) [F.LaxMonoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 元の基点の単位への像を基点とする、同じ写した実値。 -/
def coaugmentedPointedObject (X : PointedSSetObject.{u}) : PointedSSetObject.{u} :=
  ⟨Under.mk (X.obj.hom ≫ η.app X.obj.right)⟩

/-- 元の全 basedHom を閉 Hom に含め、同じ全入力を写した実値へ作用させる。 -/
def coaugmentedPointedInternalFunctor :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} SSetInternalObject.{u} :=
  pointedSSetObjectClosedForget.comp SSet (coaugmentedClosedEnrichedFunctor F η)

/-- 元の基点の単位への像は、全 basedHom パラメータで厳密に保存される。 -/
lemma coaugmentedPointedAction_basepoint (X Y : PointedSSetObject.{u}) :
    ((coaugmentedPointedObject F η X).obj.hom ▷ (X ⟶[SSet.{u}] Y)) ≫
      uncurry ((coaugmentedPointedInternalFunctor F η).map X Y) =
        toUnit _ ≫ (coaugmentedPointedObject F η Y).obj.hom := by
  have hb := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint X.obj Y.obj
    (𝟙 (PointedObject.basedHom X.obj Y.obj).right)
  rw [Category.id_comp] at hb
  change ((X.obj.hom ≫ η.app X.obj.right) ▷ (X ⟶[SSet.{u}] Y)) ≫
    uncurry (PointedObject.basedHomι X.obj Y.obj ≫
      coaugmentedClosedFamilyMap F η X.obj.right Y.obj.right) = _
  rw [comp_whiskerRight, Category.assoc, coaugmentedClosedFamilyMap_action,
    ← Category.assoc]
  exact (congrArg (fun q => q ≫ η.app Y.obj.right) hb).trans (Category.assoc _ _ _)

/-- 元の全 basedHom パラメータを保持する、写した実値間の標準 basedHom への族。 -/
def coaugmentedPointedFamilyMap (X Y : PointedSSetObject.{u}) :
    (X ⟶[SSet.{u}] Y) ⟶
      (coaugmentedPointedObject F η X ⟶[SSet.{u}] coaugmentedPointedObject F η Y) :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry (coaugmentedPointedObject F η X).obj
    (coaugmentedPointedObject F η Y).obj
    (uncurry ((coaugmentedPointedInternalFunctor F η).map X Y))
    (coaugmentedPointedAction_basepoint F η X Y)

/-- 全 basedHom 族の包含後には、元の同じ閉 Hom 作用を厳密に回収する。 -/
lemma coaugmentedPointedFamilyMap_inclusion (X Y : PointedSSetObject.{u}) :
    coaugmentedPointedFamilyMap F η X Y ≫
      pointedSSetObjectClosedForget.map (coaugmentedPointedObject F η X)
        (coaugmentedPointedObject F η Y) =
      curry (uncurry ((coaugmentedPointedInternalFunctor F η).map X Y)) :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι _ _ _ _

/-- 同じ元の基点の像と全入力を保持する、標準点つき値の厳密豊穣関手。 -/
def coaugmentedPointedEnrichedFunctor :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedSSetObject.{u} :=
  pointedEnrichedFunctorOfAction (coaugmentedPointedObject F η)
    (fun X Y => uncurry ((coaugmentedPointedInternalFunctor F η).map X Y))
    (internalEnrichedAction_unit (coaugmentedPointedInternalFunctor F η))
    (internalEnrichedAction_comp (coaugmentedPointedInternalFunctor F η))
    (coaugmentedPointedFamilyMap F η) (coaugmentedPointedFamilyMap_inclusion F η)

end SerrePositivity.KST.SConstruction
