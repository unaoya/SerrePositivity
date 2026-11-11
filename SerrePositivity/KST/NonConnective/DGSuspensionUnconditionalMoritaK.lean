module
public import SerrePositivity.KST.NonConnective.DGSuspensionUnconditionalMorita
public import SerrePositivity.KST.NonConnective.DGKInputDerivedMorita
public import SerrePositivity.KST.NonConnective.DGKappaRawSuspensionCompletion

/-!
概要：新提供者の元の厳密懸垂射に対し、同じ固定 K 射の全整数 π 同型を得る。
方針：元の実商同値から同じ主 Perf 延長の同値性を導き、元の BF Morita 定理へ代入する。
規約：全反復の自然性と非連結化後の Morita 不変性は別工程。
使われ方：K-7 e の一回の実懸垂段の固定 K 比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance suspensionMoritaKSimplicialCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B)
  [(dgDerivedExtension R A B (perfDGInputHomEquiv R A B f)).IsEquivalence]

/-- 元の同じ懸垂入力射の主 Perf 延長は同値。 -/
theorem dgKappaUnconditionalSuspensionPerfectExtension_isEquivalence_of_morita :
    (quasiEquivalencePerfectExtension R _ _
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionInputMap R A B
        (perfDGInputHomEquiv R A B f) κ hκ).down).IsEquivalence := by
  let : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (dgKappaSuspensionKInput R A
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R A κ hκ)) :=
    dgKappaSuspension_isDGPretriangulated R A (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R A κ hκ)
  let : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (dgKappaSuspensionKInput R B
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R B κ hκ)) :=
    dgKappaSuspension_isDGPretriangulated R B (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R B κ hκ)
  exact dgKappaPerfectExtension_isEquivalence_of_native R _ _ _
    (dgKappaUnconditionalSuspensionInputMap_isQCatEquivalence_of_morita R κ hκ f)

/-- 同じ実懸垂入力射は全主導来 Morita 同値も保つ。 -/
theorem dgKappaUnconditionalSuspensionDerivedExtension_isEquivalence_of_morita :
    (dgDerivedExtension R _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionInputMap R A B
      (perfDGInputHomEquiv R A B f) κ hκ).down).IsEquivalence := by
  let := dgKappaUnconditionalSuspensionPerfectExtension_isEquivalence_of_morita R κ hκ f
  exact dgKInputDerivedExtension_isEquivalence_of_perfect R _ _ _

/-- 同じ元の実懸垂入力射の固定 K 射は全整数 π 同型。 -/
theorem dgKappaUnconditionalSuspensionKMap_piIsomorphism_of_morita :
    OmegaSpectrum.PiIsomorphism (dgKInputSpectrumMap R
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionInputMap R A B
        (perfDGInputHomEquiv R A B f) κ hκ)) := by
  let := dgKappaUnconditionalSuspensionPerfectExtension_isEquivalence_of_morita R κ hκ f
  exact presentedPerfectDGBFMap_morita_piIsomorphism R _

/-- 同じ固定 K の元の辺は Sp で可逆。 -/
theorem dgKappaUnconditionalSuspensionKMap_isInvertible_of_morita :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputSpectrumMap R
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionInputMap R A B
        (perfDGInputHomEquiv R A B f) κ hκ))) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (dgKappaUnconditionalSuspensionKMap_piIsomorphism_of_morita R κ hκ f)

end SerrePositivity.KST.NonConnective
