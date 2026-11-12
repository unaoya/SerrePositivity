module
public import SerrePositivity.KST.Fibration.StableArrowReconstruction
public import SerrePositivity.KST.Fibration.VerdierFullSZeroCornerKanMap

/-!
概要：零中間頂点を持つ元の安定二胞体の、全 S• 中間対象への厳密な因子分解。
方針：元の短辺を回収し、指定長 Hom の全 S• 延長と元の core 制限を照合する。
規約：元の二胞体・全長 Hom・元の短辺を保持する。
使われ方：coherent 中間対象輸送を元の Verdier 上側二胞体へ適用する実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))

include hZ in
/-- 元の上側二胞体の第一短辺は、同じ指定零中間頂点への零値完全関手。 -/
theorem zeroMiddleTriangle_first_zero :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 s)).hom) :=
  isZeroVertex_functorVertex_of_pointwise _ (fun _ => hZ _)

/-- 全 S• への中間対象変更は、同じ第一短辺の元の全 S• 実作用である。 -/
def zeroMiddleFullSKanComparison :
    fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩) ⟶
      stableCoreSingleKanObject (s.obj ⟨ULift.up 1⟩) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map
    (zeroFunctorFullSMap (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 s))
      (zeroMiddleTriangle_first_zero s hZ)))

/-- 同じ元の第一短辺から作った中間対象比較の辺自体が可逆。 -/
theorem zeroMiddleFullSKanComparison_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (zeroMiddleFullSKanComparison s hZ)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isQCatEquivalence_of_anodyneQ_isIso
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff _).mpr
    (zeroFunctorFullSMap_localized_isIso _ _ hZ)

/-- 元の第一短辺の同じ core S Kan 射は、同じ実 core 包含と可逆比較の厳密合成。 -/
theorem zeroMiddleFullSKanComparison_first :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (s.obj ⟨ULift.up 0⟩)) ≫
        zeroMiddleFullSKanComparison s hZ =
      stableCoreSingleKanMap (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 s)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _
  rw [← Functor.map_comp, coreSFullRealizationInclusion, ← Functor.map_comp]
  exact congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map f))
    (by
      simpa only [Category.assoc] using
        (zeroFunctorFullSMap_core (𝟙 (s.obj ⟨ULift.up 0⟩).obj)
          (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 s)) (zeroMiddleTriangle_first_zero s hZ)))

/-- 元の native 第一短辺は、同じ回収完全射の元の実 core S Kan 射そのもの。 -/
theorem zeroMiddleCoreSingleKanTriangle_first :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 2 ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
      (Opposite.op ⦋2⦌) s) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (stableCoreSingleKanMap (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 s)))).edge := by
  have h := ConcreteCategory.congr_hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).naturality
      (SimplexCategory.δ (2 : Fin 3)).op) s
  exact h.symm.trans (stableCoreSingleKan_edge_reconstruct _)

/-- 元の native 第二短辺も、同じ回収完全射の元の実 core S Kan 射そのもの。 -/
theorem zeroMiddleCoreSingleKanTriangle_last :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
      (Opposite.op ⦋2⦌) s) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (stableCoreSingleKanMap (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 s)))).edge := by
  have h := ConcreteCategory.congr_hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).naturality
      (SimplexCategory.δ (0 : Fin 3)).op) s
  exact h.symm.trans (stableCoreSingleKan_edge_reconstruct _)

/-- 元の長 Hom の全族を、同じ全 S• 始域の Kan 関手族へ延長する。 -/
def zeroMiddleFullSKanLongHom :
    nerve (CategoryTheory.SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶
        (ihom (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩)).obj).obj
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)).obj :=
  stableTriangleZeroHomLift s hZ ≫
    zeroFunctorFullSKanFamily (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)

/-- 全 S• 延長の実 core 制限は、元の指定二胞体の全長 Hom へ厳密に戻る。 -/
theorem zeroMiddleFullSKanLongHom_core :
    zeroMiddleFullSKanLongHom s hZ ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion
          (s.obj ⟨ULift.up 0⟩)))).app (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)).obj =
      coherentTriangleLongHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s) := by
  rw [zeroMiddleFullSKanLongHom, Category.assoc, zeroFunctorFullSKanFamily_core,
    ← Category.assoc, stableTriangleZeroHomLift_recovery]
  rfl

end SerrePositivity.KST.Fibration
