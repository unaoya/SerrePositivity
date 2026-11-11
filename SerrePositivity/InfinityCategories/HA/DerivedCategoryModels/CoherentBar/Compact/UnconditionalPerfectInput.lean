module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UnconditionalConeInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.Input
/-!
概要：無条件 cone 入力に、D-e の実 Perf 比較と充満忠実性を代入する。
方針：同じ実代表系の cone を一度固定し、既存の全関手比較を使う。
規約：比較同値や包含同型を新しい仮定に残さない。
使われ方：D-8 e の DGKappaPerfectInput と K-B への公開入口。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

/-- 同じ無条件 cone 入力に付随する、元の実 Perf 比較。 -/
def dgKappaPerfectInput_unconditional :
    DGKappaPerfectInput R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional R D κ hκ) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional R D κ hκ)

/-- 同じ無条件 cone の実導来比較は全写像空間で充満忠実。 -/
lemma dgKappaConeInput_unconditional_derivedFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgKappaConeDerivedComparison R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional R D κ hκ)) :=
  dgKappaConeDerivedComparison_isFullyFaithful R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional R D κ hκ)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
