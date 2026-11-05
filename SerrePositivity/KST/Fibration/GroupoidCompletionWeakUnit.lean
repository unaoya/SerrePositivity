module
public import SerrePositivity.InfinityCategories.Derived.Localization.GroupoidCompletion
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy

/-! # 元の全辺局所化の単位と Kan 標的による全写像空間の検査 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- Kan 標的への全関手は指定した全辺を反転し、反転関手の包含は元の全関手圏との同型。 -/
def invertingFunctorsToKanIso (X Z : SSet.{u}) [KanComplex Z] (W : Set (X _⦋1⦌)) :
    (invertingFunctors X Z W : SSet.{u}) ≅ (ihom X).obj Z where
  hom := (invertingFunctors X Z W).ι
  inv := fullSubcomplexLift (IsInvertingFunctorVertex X Z W) (𝟙 _) (by
    intro v s _
    exact invertsAllEdges_toKan ((functorVertexEquiv X Z).symm v) (Set.mem_univ s))
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    rfl
  inv_hom_id := fullSubcomplexLift_ι _ _ _

/-- 亜群化の同じ単位への前合成は、Kan 標的の全関手 ∞ 圏の同値。 -/
theorem groupoidCompletionUnit_precompose_isQCatEquivalence (X Z : SSet.{u}) [KanComplex Z] :
    IsQCatEquivalence ((pre (groupoidCompletionMap X)).app Z) := by
  rw [← localizationPrecomposition_ι (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap X) Set.univ
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion_isLocalization X).choose Z]
  exact ((groupoidCompletion_isLocalization X).choose_spec Z).comp
    (qCatEquivalenceOfIso (invertingFunctorsToKanIso X Z Set.univ)).isQCatEquivalence

/-- 元の亜群化単位は、全 Kan 標的への写像空間で検査する弱ホモトピー同値。 -/
theorem groupoidCompletionUnit_isWeakHomotopyEquivalence (X : SSet.{u}) :
    IsWeakHomotopyEquivalence (groupoidCompletionMap X) := by
  intro Z _
  have he := groupoidCompletionUnit_precompose_isQCatEquivalence X Z
  exact he.isSimplicialHomotopyEquivalence.mapPiZero_bijective

end SerrePositivity.KST.Fibration
