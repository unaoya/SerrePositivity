module
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSDiagramFamily
public import SerrePositivity.KST.Fibration.CoreSingleKanFamily
public import SerrePositivity.KST.Fibration.ZeroStableHomRelativeComparison

/-!
概要：元の零値関手の全 S• 作用を、同じ全 S• 実現の Ex∞ Hom へ送る。
方針：標準図式 Hom の対角作用と Ex∞ の全閉 Hom 作用を合成する。
規約：始域の全 S• を保持し、指定した元の完全関手の実現射を厳密に回収する。
使われ方：商核上辺と元の Verdier 二胞体の全パラメータ比較。
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

/-- 元の全 S• の対角を、そのまま Ex∞ Kan 値として保持する。 -/
def fullSRealizationKanObject (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  exInfinityClosedKanEnrichedFunctor.obj
    (simplicialSSetDiagramDiagonalEnrichedFunctor.obj ⟨simplicialSConstruction A.obj⟩)

/-- 元の零値関手の全高次族による、同じ全 S• から core S• への Ex∞ Hom 作用。 -/
def zeroFunctorFullSKanFamily (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    zeroFunctorLocus A C ⟶
      (fullSRealizationKanObject A ⟶[SSet.{u}] stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)) :=
  zeroFunctorFullSDiagramFamily A C ≫
    simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _ ≫
      exInfinityClosedKanEnrichedFunctor.map _ _

/-- 同じ指定点では、元の全 S• 零値作用の同じ実現射の Ex∞ 表示を回収する。 -/
theorem zeroFunctorFullSKanFamily_fixed {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    zeroFunctorParameterPoint F hF ≫ zeroFunctorFullSKanFamily A C =
      eHomEquiv SSet (show fullSRealizationKanObject A ⟶
        stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C) from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (zeroFunctorFullSMap F hF))) := by
  rw [zeroFunctorFullSKanFamily, ← Category.assoc, ← Category.assoc,
    zeroFunctorFullSDiagramFamily_fixed, simplicialSSetDiagramDiagonalEnrichedFunctor_hom]
  exact exInfinityClosedKanEnrichedFunctor_hom _

/-- 同じ全円柱の Ex∞ 評価は、元の実現円柱の strength による像と厳密一致。 -/
theorem zeroFunctorFullSKanFamily_action (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    uncurry (zeroFunctorFullSKanFamily A C) =
      coaugmentedTensorRightStrength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
          (simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj)) (zeroFunctorLocus A C) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialCylinderDiagonal _ _ (zeroFunctorLocus A C)
          (zeroFunctorFullSCoreNatTrans A C)) := by
  rw [zeroFunctorFullSKanFamily, ← Category.assoc]
  exact (coaugmentedClosedFamilyMap_strength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
    (zeroFunctorFullSDiagramFamily A C ≫
      simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _)).trans
    (congrArg (fun f => coaugmentedTensorRightStrength _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
      (simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj)) (zeroFunctorLocus A C) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map f) (zeroFunctorFullSDiagramFamily_diagonal A C).symm)

end SerrePositivity.KST.Fibration
