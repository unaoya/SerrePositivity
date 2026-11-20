module


public import SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullbackSquare
public import SerrePositivity.KST.Spectra.CoherentCospanLimits

/-!
概要：元の E(A) は、元の商の二脚の選択した ∞ pullback と同値。
方針：同じ cospan 上の二つの実極限錐の同型を取り、頂点へ写す。
規約：錐全体の比較も公開する。使われ方：Land–Tamme の抽象 pullback 同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback
end SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientPullbackComparison
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback
local instance pullbackComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def chosenCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (cospan hΦ p q i r h) :=
  OmegaSpectrum.CoherentPullback.infinityCone (cospan hΦ p q i r h)

lemma chosenCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientPullbackComparison.chosenCone hΦ p q i r h) :=
  OmegaSpectrum.CoherentPullback.infinityCone_isLimit (cospan hΦ p q i r h)

def coneComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (cospan hΦ p q i r h))
    (cone hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientPullbackComparison.chosenCone hΦ p q i r h) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso _ _ (cone_isLimit hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientPullbackComparison.chosenCone_isLimit hΦ p q i r h)

def valueIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := Sp.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (value Φ A))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientPullbackComparison.chosenCone hΦ p q i r h).vertex := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso (cone hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientPullbackComparison.chosenCone hΦ p q i r h)
    (cone_isLimit hΦ p q i r h) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientPullbackComparison.chosenCone_isLimit hΦ p q i r h)
  have hv : (HomotopyCategory.mk (cone hΦ p q i r h).vertex : hoFunctor.obj Sp.{u}) =
      SpectrumHo.obj (value Φ A) := congrArg HomotopyCategory.mk (cone_vertex hΦ p q i r h)
  exact eqToIso hv.symm ≪≫ e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientPullbackComparison

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
