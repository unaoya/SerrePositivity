module

public import SerrePositivity.KST.LocalizingInvariants.VerdierRelativeConeSimplex
public import SerrePositivity.KST.LocalizingInvariants.RelativeConeFunctorComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.FiniteQuotientConeRecoveryCofinality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSimplexCompletionComparison

/-!
概要：元の第一行単体商射は、零次を含む全次数で anodyne 局所化により可逆になる。
方針：全有限境界付き商錐の回収から元の core 逆像射影の cofinality を証明する。
規約：元の完成比較の全 Hom 充満忠実性を証明し、同じ元の商射の判定へ代入する。
使われ方：K-B c5 の正式依頼型を追加仮定なしで供給する Sp 正本。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の第一行単体商射そのものは、零次を含む全次数で left cofinal。 -/
lemma relativeFirstRowSimplexQuotient_isLeftCofinal
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (relativeFirstRowSimplexQuotient q n) := by
  apply corePreimageProjection_isLeftCofinal_of_quotientConeRecovery
    ((ihom (Δ[n] : SSet.{u})).map q.hom)
  intro K _ p t
  exact quotientFunctorConeIsoRecovery_of_relativeConeRecovery q.hom Δ[n]
    (hasVerdierRelativeConeRecovery_simplex h n) K p t

/-- 元の完成比較の全 pinched Hom は、零次を含む全次数で同値。 -/
lemma relativeFirstRowSimplexCompletionComparison_isFullyFaithful
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison q n) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexQuotient_localized_isIso_iff_fullyFaithful h n).mp
    (weakHomotopyEquivalence_anodyneQ_isIso _
      (relativeFirstRowSimplexQuotient_isLeftCofinal h n).isWeakHomotopyEquivalence)

/-- 元の全 Hom 充満忠実性の判定へ代入した、全次数の正式な単体商局所化供給。 -/
lemma relativeFirstRowSimplexQuotient_localized_isIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowSimplexQuotient q n)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexQuotient_localized_isIso_iff_fullyFaithful h n).mpr
    (relativeFirstRowSimplexCompletionComparison_isFullyFaithful h n)

/-- K-B c5 の依頼型そのもの。零次を除外せず、元の Verdier 列の射影を使う。 -/
theorem VerdierSequence.relativeFirstRowSimplexQuotient_localized_isIso
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u}) :
    ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowSimplexQuotient h.projection n)) :=
  fun n =>
    SerrePositivity.KST.LocalizingInvariants.relativeFirstRowSimplexQuotient_localized_isIso
      h.isVerdier n

end SerrePositivity.KST.LocalizingInvariants
