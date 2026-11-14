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
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

def tammeArrowQuotient : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.stableArrowCategory (laxCategory p q)).obj (tammeArrowLocalizingEdges p q)

instance tammeArrowQuotient_quasicategory : Quasicategory (tammeArrowQuotient p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization_quasicategory _ _

instance tammeArrowQuotient_hasZeroVertex : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (tammeArrowQuotient p q) :=
  edgeLocalization_hasZeroVertex _ _

def tammeArrowQuotientMap : (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.stableArrowCategory (laxCategory p q)).obj ⟶
    tammeArrowQuotient p q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalizationMap _ _

lemma tammeArrowQuotient_isLocalization : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (tammeArrowQuotientMap p q)
    (tammeArrowLocalizingEdges p q) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization_isLocalization _ _

lemma tammeArrowProjection_inverts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((ihom (Δ[1] : SSet.{u})).map (tammeQuotientMap p q))
      (tammeArrowLocalizingEdges p q) := by
  rw [tammeArrowLocalizingEdges_eq_invertedQuotient]
  exact Set.Subset.refl _

def tammeArrowQuotientComparison : tammeArrowQuotient p q ⟶
    (ihom (Δ[1] : SSet.{u})).obj (tammeQuotient p q) :=
  localizationDescend _ _ (tammeArrowQuotient_isLocalization p q) _
    (tammeArrowProjection_inverts p q)

def tammeArrowQuotientComparisonIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (tammeArrowQuotientMap p q ≫ tammeArrowQuotientComparison p q)
    ((ihom (Δ[1] : SSet.{u})).map (tammeQuotientMap p q)) :=
  localizationDescendIso _ _ (tammeArrowQuotient_isLocalization p q) _
    (tammeArrowProjection_inverts p q)

lemma tammeArrowQuotientComparison_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (tammeArrowQuotientComparison p q) := by
  intro v
  obtain ⟨x, ⟨e⟩⟩ := tammeQuotientArrow_isEssentiallySurjective p q v
  exact ⟨(tammeArrowQuotientMap p q).app (Opposite.op ⦋0⦌) x,
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (tammeArrowQuotientComparisonIso p q) x ≪≫ e⟩⟩

lemma tammeArrowQuotientMap_invertedEdges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (tammeArrowQuotientMap p q) = tammeArrowLocalizingEdges p q := by
  apply Set.Subset.antisymm
  · have h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (tammeArrowQuotientMap p q ≫ tammeArrowQuotientComparison p q)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (tammeArrowQuotientMap p q)) :=
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (tammeArrowQuotientMap p q)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (tammeArrowQuotientMap p q)) from Set.Subset.refl _).comp _
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges at h
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.invertedEdges_functorIso (tammeArrowQuotientComparisonIso p q),
      ← tammeArrowLocalizingEdges_eq_invertedQuotient] at h
    exact h
  · exact (tammeArrowQuotient_isLocalization p q).choose

def tammeArrowQuotientCofiber : tammeArrowQuotient p q ⟶ tammeQuotient p q :=
  localizationDescend _ _ (tammeArrowQuotient_isLocalization p q) _
    (tammeCofiber_quotient_inverts p q)

def tammeArrowQuotientCofiberIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (tammeArrowQuotientMap p q ≫ tammeArrowQuotientCofiber p q)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber (laxCategory p q).obj (𝟙 _) ≫ tammeQuotientMap p q) :=
  localizationDescendIso _ _ (tammeArrowQuotient_isLocalization p q) _
    (tammeCofiber_quotient_inverts p q)

end SerrePositivity.KST.LocalizingInvariants
