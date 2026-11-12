module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportDiagramInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictTransportMappingEquivalence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.CoreEnrichedFunctor
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.CoreEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveFullyFaithful
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の cocartesian strict transport を全相対 Hom の core に作用する豊穣関手へ束ねる。
方針：同じ単位・合成の等式を core 関手で移し、全 Hom の同値を coherent nerve で検出する。
規約：分類主写像の充満忠実性と、中間の像への充満忠実性を区別する。
使われ方：Cat∞ 値分類写像の実際の Hom 作用を回収する入力。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- strict transport の同じ元の全相対作用は単位と合成を保つ豊穣関手。 -/
def cocartesianStrictTransportEnriched {C : Type u} [Category.{u} C] :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramObject C) where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramImage
  map p q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportMappingSpaceMap p.val.hom q.val.hom
  map_id p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportMappingSpaceMap_identity p.val.hom
  map_comp p q r := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportMappingSpaceMap_composition
    p.val.hom q.val.hom r.val.hom

/-- 元の全相対 Hom の core 上に制限した同じ strict transport の豊穣関手。 -/
def cocartesianStrictTransportCoreEnriched {C : Type u} [Category.{u} C] :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor (cocartesianStrictTransportEnriched (C := C))

/-- 全相対 Hom の core に作用する同じ比較を coherent nerve の射へ実現する。 -/
def cocartesianStrictTransportInfinityMap (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramInfinity C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (cocartesianStrictTransportCoreEnriched (C := C))

/-- 元の core 上の Hom 作用は、全相対作用の同値性から同値。 -/
lemma cocartesianStrictTransportCoreEnriched_map_isQCatEquivalence
    {C : Type u} [Category.{u} C] (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((cocartesianStrictTransportCoreEnriched (C := C)).map p q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMappingSpaceMap_isQCatEquivalence p.val.hom q.val.hom).core

/-- 中間の strict transport 図式の ∞ 圏への、同じ coherent な比較は充満忠実。 -/
@[kerodon 037V]
lemma cocartesianStrictTransportInfinityMap_isFullyFaithful (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (cocartesianStrictTransportInfinityMap C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff
    (cocartesianStrictTransportCoreEnriched (C := C))).mpr
  exact cocartesianStrictTransportCoreEnriched_map_isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
