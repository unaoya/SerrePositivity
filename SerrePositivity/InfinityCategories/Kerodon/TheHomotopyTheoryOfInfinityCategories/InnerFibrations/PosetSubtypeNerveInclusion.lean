module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeNerve
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping

/-!
概要：順序部分型の図式を元の順序集合へ厳密に延長する。
方針：全部分複体の同型と、有限局所余極限・指定終対象への延長を接続する。
規約：元の図式と指定した終対象を保持する。使われ方：一般安定性判定の比較格子。

対応節は Kerodon 4.1（Tag 01B8）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
instance posetSubtypeInclusion_nerveMap_mono {P : Type u} [PartialOrder P] (T : P → Prop) :
    Mono (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso_hom_ι T]
  infer_instance

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
instance posetSubtypeInclusion_nerveMap_innerFibration {P : Type u} [PartialOrder P]
    (T : P → Prop) : InnerFibration (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso_hom_ι T]
  infer_instance

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
lemma posetSubtypeInclusion_nerveMap_isFullyFaithful {P : Type u} [PartialOrder P]
    (T : P → Prop) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso_hom_ι T]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso T)).isQCatEquivalence.isFullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations
