module
public import SerrePositivity.KST.Fibration.VerdierFullSZeroCornerKanMap
public import SerrePositivity.KST.Fibration.CoreSingleKanCoordinates

/-!
概要：全 S• 零角の同じ指定比較を、元の正反復 Kan 実現の対象座標へ戻す。
方針：元の core S 座標同型を前後に用い、指定左辺の同じ実現射を回収する。
規約：比較の実射と指定辺を保持し、対象等号による座標だけを輸送する。
使われ方：元の Verdier 二胞体を含む native 四角形との比較入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

/-- 元の native core S(A) 座標から、同じ全 S(A) の実 Kan 値への実包含。 -/
def fullSNativeCoreInclusion (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableMultiKanEnrichedFunctor 0).obj A ⟶ fullSRealizationKanObject A :=
  (coreSingleKanIso A).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion A)

/-- 元の native 零角座標を標的にする、同じ指定左辺の全 S• 比較。 -/
def verdierFullSZeroCornerNativeKanMap (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    fullSRealizationKanObject d.left ⟶
      (stableMultiKanEnrichedFunctor 0).obj
        (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 0 1)) :=
  verdierFullSZeroCornerKanMap d ≫
    (coreSingleKanIso (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 0 1))).hom

set_option maxHeartbeats 800000 in
-- 元の native 対象と core S 座標を同時に照合するための展開に使用する。
/-- 元の指定左辺の native 実現は、同じ元の全 S• 零角を通る厳密合成。 -/
theorem verdierFullSZeroCornerNativeKanMap_left (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    fullSNativeCoreInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ≫
        verdierFullSZeroCornerNativeKanMap d =
      (show (stableMultiKanEnrichedFunctor 0).obj (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
        (stableMultiKanEnrichedFunctor 0).obj
          (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 0 1)) from
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map ((multiRealizationFunctor 1).map
          (stableExactInputMap (verdierLeftExactMap d)))) := by
  rw [fullSNativeCoreInclusion, verdierFullSZeroCornerNativeKanMap]
  simp only [Category.assoc]
  erw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))),
    verdierFullSZeroCornerKanMap_left]
  erw [coreSingleKanIso_naturality (verdierLeftExactMap d)]
  exact Iso.inv_hom_id_assoc _ _

/-- 元の native 上辺も、同じ実比較と元の上側全 S• 合成の厳密な因子分解を保つ。 -/
theorem verdierFullSZeroCornerNativeKanMap_top (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierFullSZeroCornerNativeKanMap d ≫
        (show (stableMultiKanEnrichedFunctor 0).obj
          (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 0 1)) ⟶
            (stableMultiKanEnrichedFunctor 0).obj (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map ((multiRealizationFunctor 1).map
            (stableExactInputMap (verdierTopExactMap d)))) =
      (show fullSRealizationKanObject d.left ⟶
        (stableMultiKanEnrichedFunctor 0).obj (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map
            (zeroFunctorFullSMap (verdierNullCompositeOriginalMap d 0)
              (verdierUpperComposite_zero d))) ≫
              (coreSingleKanIso (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).hom) := by
  rw [verdierFullSZeroCornerNativeKanMap, Category.assoc,
    ← coreSingleKanIso_naturality (verdierTopExactMap d), ← Category.assoc]
  exact congrArg (· ≫ (coreSingleKanIso (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).hom)
    (verdierFullSZeroCornerKanMap_top d)

/-- 同じ指定比較の辺は、元の native 対象座標へ戻した後も可逆。 -/
theorem verdierFullSZeroCornerNativeKanMap_isInvertible (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (verdierFullSZeroCornerNativeKanMap d)) := by
  let Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 0 1)
  let E : (stableCoreSingleKanObject Z).obj ≅ ((stableMultiKanEnrichedFunctor 0).obj Z).obj :=
    { hom := (coreSingleKanIso Z).hom
      inv := (coreSingleKanIso Z).inv
      hom_inv_id := (coreSingleKanIso Z).hom_inv_id
      inv_hom_id := (coreSingleKanIso Z).inv_hom_id }
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (verdierFullSZeroCornerKanMap d) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isQCatEquivalence_of_anodyneQ_isIso
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff _).mpr
      (zeroFunctorFullSMap_localized_isIso _ _ d.zero_corner)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
    (he.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso E).isQCatEquivalence)

end SerrePositivity.KST.Fibration
