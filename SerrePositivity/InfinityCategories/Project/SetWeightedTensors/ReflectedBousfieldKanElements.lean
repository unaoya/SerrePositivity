module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.ReflectedBousfieldKanUnderWeight
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UnderWeightedColimitNormalization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimitWeightTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.ReflectedBousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetElements

/-!
概要：集合値係数の同じ反転 BK coend を、元の圏の nerve で表示する。
方針：指定した重みの自然同型と既存 replacement への比較を、既存 elementsToReplacement へ合成する。
規約：Kerodon §7.5（Tag 039Y）、Construction 5.3.2.1（Tag 035V）の既存模型の係数移送。
使われ方：S8 の Čech 解消の余極限性。生の集合の余極限とは同一視しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors
variable {I : Type u} [SmallCategory I]

/-- 同じ反転 BK coend と同じ replacement の、指定全比較の合成。 -/
def reflectedBousfieldKanReplacementIso (F : I ⥤ SSet.{u}) :
    reflectedBousfieldKanColimit F ≅ simplicialReplacement F :=
  weightedColimitWeightIso (reflectedBousfieldKanUnderWeightIso I) F ≪≫
    underWeightedColimitReplacementIso F

/-- 集合値係数では、既存の元の圏の同型へ接続する。 -/
def reflectedBousfieldKanElementsIso (P : I ⥤ Type u) :
    reflectedBousfieldKanColimit (coefficients P) ≅ nerve P.Elements :=
  reflectedBousfieldKanReplacementIso (coefficients P) ≪≫ (asIso (elementsToReplacement P)).symm

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
