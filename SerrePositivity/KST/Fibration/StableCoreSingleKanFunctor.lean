module
public import SerrePositivity.KST.Fibration.CoreSingleCoordinates
public import SerrePositivity.KST.Fibration.EnrichedObjectRelabelling
public import SerrePositivity.KST.Fibration.StableBoundaryKanComparison

/-! # 元の core S 実現を値として明示する、全 Hom を持つ同じ一回の実現関手 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 同じ元の core S 実現の Ex∞ Kan 値。 -/
def stableCoreSingleKanObject (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  exInfinityClosedKanEnrichedFunctor.obj ⟨coreSRealizationFunctor.obj (stableCategoryModel C)⟩

/-- 一回の反復実現と元の core S 実現は、同じ Ex∞ Kan 対象として等しい。 -/
theorem stableCoreSingleKan_object_eq (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableMultiKanEnrichedFunctor 0).obj C = stableCoreSingleKanObject C :=
  congrArg (fun V : SSet.{u} => exInfinityClosedKanEnrichedFunctor.obj ⟨V⟩)
    (coreSingleRealization_obj_eq (stableCategoryModel C)).symm

/-- 元の core S 実現を対象表示に使い、同じ全 Hom 作用を保持する。 -/
def stableCoreSingleKanEnrichedFunctor :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  relabelEnrichedObjects (stableMultiKanEnrichedFunctor 0) stableCoreSingleKanObject
    (funext stableCoreSingleKan_object_eq)

/-- 元の全 Hom の関手を変えず、対象の座標だけを読み替えた同じ豊穣関手である。 -/
theorem stableCoreSingleKanEnrichedFunctor_eq :
    stableCoreSingleKanEnrichedFunctor.{u} = stableMultiKanEnrichedFunctor 0 :=
  relabelEnrichedObjects_eq _ _ _

/-- 同じ全高次単体を持つ、元の core S 実現と一回の反復実現の ∞ 関手の等号。 -/
theorem stableCoreSingleKanInfinity_eq :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor.{u} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0) :=
  congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor_eq

end SerrePositivity.KST.Fibration
