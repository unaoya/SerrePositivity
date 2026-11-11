module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftPathStrictification
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.HomotopyEquivalencePath

/-!
概要：底で恒等な指定相対左 Kan 単位から元と標的を保つ厳密化を構成する。
方針：指定単位の可逆性を反映し、その同じ代表から底で定値な可逆 path を作る。
規約：部分図式と底の図式を等式で保つ。底での定値性は代表自体への条件。
使われ方：相対 Kan 制限の元の関手圏での厳密な存在。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：底で定値な指定相対左 Kan 単位を厳密な元の図式の延長へ変換する。
方針：単位を可逆 path の族にし、元・底・終点を固定して延長する。
規約：底で恒等な代表を明示し、像の類が可逆であるだけとは区別する。
使われ方：一般の isofibration 上での元の相対左 Kan 関手の構成。 -/
lemma exists_kanRelativeLeftCanonical_strictification_of_unit_over_identity
    {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀ F β)
    (hfixed : β.h ≫ U = fst K (Δ[1] : SSet.{u}) ≫ (δ ≫ (F ≫ U))) :
    ∃ G : C ⟶ D, δ ≫ G = F₀ ∧ G ≫ U = F ≫ U ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ G := by
  have : InnerFibration U := hU.innerFibration
  have hiU : IsIso ((hoFunctor.map ((ihom K).map U)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopy_isInvertible_of_constant (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp β U)
      (δ ≫ (F ≫ U)) hfixed
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanExtension_unit_isIso δ hδ U β hβ hiU
  have hF := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanExtension_canonical_of_unit_isIso U δ β hβ hi
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyEquivalencePath β hi
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strictification_of_path U hU δ hF a
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyEquivalencePath_zero β hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyEquivalencePath_one β hi)
  simpa only [Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanHomotopyEquivalencePath_map_of_constant β hi U (δ ≫ (F ≫ U)) hfixed

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
