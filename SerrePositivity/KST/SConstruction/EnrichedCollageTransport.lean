module
public import SerrePositivity.KST.SConstruction.EnrichedCollageComparisonDiagram
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyComposition

/-! # 全入力変換の有向 collage 内での合成
概要：F→R G の全入力変換を、下段 F から上段 G への全入力変換に移す。
方針：下段包含による像を交差恒等射の円柱と ∞ 圏内で合成する。
規約：指定した二つの円柱を実際の合成三角形の辺として保持する。
使われ方：元の Ω 構造の全入力円柱を suspension 評価へ渡す前の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]
  {I : Type u} [SmallCategory I]

/-- 元の全入力変換を下段包含で写した、指定した第一の円柱。 -/
def enrichedFunctorCollageInputHomotopy (R : EnrichedFunctor SSet.{u} C D)
    {F : I ⥤ D} {G : I ⥤ C}
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R)) :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ enrichedFunctorCollageBottomInfinity R)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R ≫
        enrichedFunctorCollageBottomInfinity R) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H (enrichedFunctorCollageBottomInfinity R)

/-- 下段の全入力変換と、指定した上段への比較円柱を ∞ 圏内で合成する。 -/
def enrichedFunctorCollageTransportHomotopy (R : EnrichedFunctor SSet.{u} C D)
    [Quasicategory (EnrichedFunctorCollageInfinity R)]
    {F : I ⥤ D} {G : I ⥤ C}
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R)) :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ enrichedFunctorCollageBottomInfinity R)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ enrichedFunctorCollageTopInfinity R) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopyComposite (enrichedFunctorCollageInputHomotopy R H)
    (enrichedFunctorCollageComparisonHomotopy R G)

/-- 元の指定した二つの全入力円柱と合成した円柱を保持する実三角形。 -/
def enrichedFunctorCollageTransportTriangle (R : EnrichedFunctor SSet.{u} C D)
    [Quasicategory (EnrichedFunctorCollageInfinity R)]
    {F : I ⥤ D} {G : I ⥤ C}
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (enrichedFunctorCollageInputHomotopy R H)
      (enrichedFunctorCollageComparisonHomotopy R G)
      (enrichedFunctorCollageTransportHomotopy R H) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopyCompositeTriangle (enrichedFunctorCollageInputHomotopy R H)
    (enrichedFunctorCollageComparisonHomotopy R G)

end SerrePositivity.KST.SConstruction
