module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback
open SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback
local instance pullbackComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def chosenCone : JoinCone (cospan hΦ p q i r h) :=
  OmegaSpectrum.CoherentPullback.infinityCone (cospan hΦ p q i r h)

lemma chosenCone_isLimit : IsLimitCone (chosenCone hΦ p q i r h) :=
  OmegaSpectrum.CoherentPullback.infinityCone_isLimit (cospan hΦ p q i r h)

def coneComparison : VertexIso (X := sliceOver (cospan hΦ p q i r h))
    (cone hΦ p q i r h) (chosenCone hΦ p q i r h) :=
  limitConeIso _ _ (cone_isLimit hΦ p q i r h) (chosenCone_isLimit hΦ p q i r h)

def valueIso : VertexIso (X := Sp.{u}) (coherentNerveVertex (value Φ A))
    (chosenCone hΦ p q i r h).vertex := by
  let e := limitVertexIso (cone hΦ p q i r h) (chosenCone hΦ p q i r h)
    (cone_isLimit hΦ p q i r h) (chosenCone_isLimit hΦ p q i r h)
  have hv : (HomotopyCategory.mk (cone hΦ p q i r h).vertex : hoFunctor.obj Sp.{u}) =
      SpectrumHo.obj (value Φ A) := congrArg HomotopyCategory.mk (cone_vertex hΦ p q i r h)
  exact eqToIso hv.symm ≪≫ e

end SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.chosenCone (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback.chosenCone := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.chosenCone

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback.chosenCone_isLimit := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.chosenCone_isLimit

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.coneComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback.coneComparison := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.coneComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.pullbackComparisonSimplicialCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback.pullbackComparisonSimplicialCategory := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.pullbackComparisonSimplicialCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.valueIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback.valueIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.valueIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback.coneComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.coneComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback.valueIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.valueIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxQuotientPullback.valueIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientPullback.valueIso._proof_2
