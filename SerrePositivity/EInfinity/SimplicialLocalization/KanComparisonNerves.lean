module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanComparisonWeak
public import SerrePositivity.EInfinity.SimplicialLocalization.Nerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
# 元の Kan 自由 hammock の左右比較の実 coherent nerve 同値

概要：同じ豊穣関手を元の coherent nerve 間の実同値へ移す。
方針：全 Kan Hom 上の同値から充満忠実性、同じ対象写像から本質的全射性を得る。
規約：元の localizationNerve と両比較を保持する。局所化の普遍性は別に証明する。
使われ方：元の通常圏から実 DK nerve への局所化関手の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Hammock SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

abbrev KanHammockCategory := ForgetEnrichment SSet.{u} (KanHammockObjects C)
abbrev KanFreeHammockCategory := ForgetEnrichment SSet.{u} (KanFreeHammockObjects C)

instance kanHammockSimplicialCategory : SimplicialCategory (KanHammockCategory C) :=
  inferInstanceAs (EnrichedOrdinaryCategory SSet.{u} (KanHammockCategory C))
instance kanFreeHammockSimplicialCategory : SimplicialCategory (KanFreeHammockCategory C) :=
  inferInstanceAs (EnrichedOrdinaryCategory SSet.{u} (KanFreeHammockCategory C))

instance kanHammockHom_kanComplex (X Y : KanHammockCategory C) :
    SSet.KanComplex (SimplicialCategory.sHom X Y) := by
  change SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y))
  infer_instance
instance kanFreeHammockHom_kanComplex (X Y : KanFreeHammockCategory C) :
    SSet.KanComplex (SimplicialCategory.sHom X Y) := by
  change SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (freeHammockDiagonal C X Y))
  infer_instance

def kanFreeHammockAugmentationFunctor :
    EnrichedFunctor SSet.{u} (KanFreeHammockCategory C) (KanHammockCategory C) :=
  kanFreeHammockAugmentationEnriched C

def kanFreeHammockComparisonFunctor :
    EnrichedFunctor SSet.{u} (KanFreeHammockCategory C) (KanLocalizationCategory C) :=
  kanFreeHammockComparisonEnriched C

def kanHammockNerve : SSet.{u} := SimplicialNerve (KanHammockCategory C)
def kanFreeHammockNerve : SSet.{u} := SimplicialNerve (KanFreeHammockCategory C)

instance kanHammockNerve_quasicategory : SSet.Quasicategory (kanHammockNerve C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory _
instance kanFreeHammockNerve_quasicategory : SSet.Quasicategory (kanFreeHammockNerve C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory _

def kanFreeHammockAugmentationNerve : kanFreeHammockNerve C ⟶ kanHammockNerve C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (kanFreeHammockAugmentationFunctor C)
def kanFreeHammockComparisonNerve : kanFreeHammockNerve C ⟶ localizationNerve C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (kanFreeHammockComparisonFunctor C)

lemma kanFreeHammockAugmentationNerve_fullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (kanFreeHammockAugmentationNerve C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff (kanFreeHammockAugmentationFunctor C)).mpr
    (fun X Y => kanFreeHammockAugmentationEnriched_map_equivalence C X Y)
lemma kanFreeHammockComparisonNerve_fullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (kanFreeHammockComparisonNerve C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff (kanFreeHammockComparisonFunctor C)).mpr
    (fun X Y => kanFreeHammockComparisonEnriched_map_equivalence C X Y)

lemma kanFreeHammockAugmentationNerve_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (kanFreeHammockAugmentationNerve C) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (kanFreeHammockAugmentationNerve_fullyFaithful C)
  intro y
  let x : KanFreeHammockCategory C :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (C := KanHammockCategory C) y
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x, ⟨eqToIso (congrArg SSet.HomotopyCategory.mk ?_)⟩⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (kanFreeHammockAugmentationFunctor C) x).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (C := KanHammockCategory C) y)

lemma kanFreeHammockComparisonNerve_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (kanFreeHammockComparisonNerve C) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (kanFreeHammockComparisonNerve_fullyFaithful C)
  intro y
  let x : KanFreeHammockCategory C :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (C := KanLocalizationCategory C) y
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x, ⟨eqToIso (congrArg SSet.HomotopyCategory.mk ?_)⟩⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (kanFreeHammockComparisonFunctor C) x).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (C := KanLocalizationCategory C) y)

end SerrePositivity.EInfinity.SimplicialLocalization
