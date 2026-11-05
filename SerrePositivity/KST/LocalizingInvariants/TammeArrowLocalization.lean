module

public import SerrePositivity.KST.LocalizingInvariants.TammeCofiberDenominators
public import SerrePositivity.KST.LocalizingInvariants.TammeQuotientArrow
public import SerrePositivity.KST.LocalizingInvariants.LocalizationZeroPreservation

/-!
概要：元の点ごとの分母による矢印圏の局所化と、元の cofiber 関手の実降下を構成する。
方針：一般局所化の全関手圏上の普遍性へ、反転を実証した二つの関手を渡す。
規約：局所化から商の実矢印圏への比較の同値性は未証明。
使われ方：cofiber 随伴の降下と、実矢印圏への移送の残る比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)

def tammeArrowQuotient : SSet.{u} :=
  edgeLocalization (_root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.stableArrowCategory (laxCategory p q)).obj (tammeArrowLocalizingEdges p q)

instance tammeArrowQuotient_quasicategory : Quasicategory (tammeArrowQuotient p q) :=
  edgeLocalization_quasicategory _ _

instance tammeArrowQuotient_hasZeroVertex : HasZeroVertex (tammeArrowQuotient p q) :=
  edgeLocalization_hasZeroVertex _ _

def tammeArrowQuotientMap : (_root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.stableArrowCategory (laxCategory p q)).obj ⟶
    tammeArrowQuotient p q := edgeLocalizationMap _ _

lemma tammeArrowQuotient_isLocalization : IsLocalization (tammeArrowQuotientMap p q)
    (tammeArrowLocalizingEdges p q) := edgeLocalization_isLocalization _ _

lemma tammeArrowProjection_inverts :
    InvertsEdges ((ihom (Δ[1] : SSet.{u})).map (tammeQuotientMap p q))
      (tammeArrowLocalizingEdges p q) := by
  rw [tammeArrowLocalizingEdges_eq_invertedQuotient]
  exact Set.Subset.refl _

def tammeArrowQuotientComparison : tammeArrowQuotient p q ⟶
    (ihom (Δ[1] : SSet.{u})).obj (tammeQuotient p q) :=
  localizationDescend _ _ (tammeArrowQuotient_isLocalization p q) _
    (tammeArrowProjection_inverts p q)

def tammeArrowQuotientComparisonIso : FunctorIso
    (tammeArrowQuotientMap p q ≫ tammeArrowQuotientComparison p q)
    ((ihom (Δ[1] : SSet.{u})).map (tammeQuotientMap p q)) :=
  localizationDescendIso _ _ (tammeArrowQuotient_isLocalization p q) _
    (tammeArrowProjection_inverts p q)

lemma tammeArrowQuotientComparison_isEssentiallySurjective :
    IsEssentiallySurjective (tammeArrowQuotientComparison p q) := by
  intro v
  obtain ⟨x, ⟨e⟩⟩ := tammeQuotientArrow_isEssentiallySurjective p q v
  exact ⟨(tammeArrowQuotientMap p q).app (Opposite.op ⦋0⦌) x,
    ⟨FunctorIso.app (tammeArrowQuotientComparisonIso p q) x ≪≫ e⟩⟩

lemma tammeArrowQuotientMap_invertedEdges :
    invertedEdges (tammeArrowQuotientMap p q) = tammeArrowLocalizingEdges p q := by
  apply Set.Subset.antisymm
  · have h : InvertsEdges (tammeArrowQuotientMap p q ≫ tammeArrowQuotientComparison p q)
        (invertedEdges (tammeArrowQuotientMap p q)) :=
      (show InvertsEdges (tammeArrowQuotientMap p q)
        (invertedEdges (tammeArrowQuotientMap p q)) from Set.Subset.refl _).comp _
    unfold InvertsEdges at h
    rw [invertedEdges_functorIso (tammeArrowQuotientComparisonIso p q),
      ← tammeArrowLocalizingEdges_eq_invertedQuotient] at h
    exact h
  · exact (tammeArrowQuotient_isLocalization p q).choose

def tammeArrowQuotientCofiber : tammeArrowQuotient p q ⟶ tammeQuotient p q :=
  localizationDescend _ _ (tammeArrowQuotient_isLocalization p q) _
    (tammeCofiber_quotient_inverts p q)

def tammeArrowQuotientCofiberIso : FunctorIso
    (tammeArrowQuotientMap p q ≫ tammeArrowQuotientCofiber p q)
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber (laxCategory p q).obj (𝟙 _) ≫ tammeQuotientMap p q) :=
  localizationDescendIso _ _ (tammeArrowQuotient_isLocalization p q) _
    (tammeCofiber_quotient_inverts p q)

end SerrePositivity.KST.LocalizingInvariants
