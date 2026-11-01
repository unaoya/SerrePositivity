module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceMapping
public import SerrePositivity.KST.LocalizingInvariants.ReflectiveMappingAdjunction
public import SerrePositivity.InfinityCategories.Stable.Verdier.AdjointVerdier

/-!
概要：q が充満忠実な右随伴を持つとき、差の関手の実右随伴と商の普遍性を構成。
方針：ρ の切断同型と元の差の写像空間比較から随伴を作り、可逆余単位で局所化する。
規約：核の一致と局所化普遍性を双方証明。使われ方：Tamme Prop. 11・Cor. 12。
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
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (v : E.obj ⟶ D.obj) (a : QCatAdjunction q.hom v) (hv : IsFullyFaithful v)

/-- 元の差の関手の右随伴は、元の D 包含と v の合成。 -/
def laxDifferenceAdjunction : QCatAdjunction (laxDifference p q) (laxDifferenceRho p q v) :=
  adjunctionOfReflectiveMapping (laxDifferenceRho_sectionIso p q v a hv)
    (laxDifferenceMapping_equivalence p q v a hv)

lemma laxDifferenceAdjunction_counitHom_isIso :
    IsIso (laxDifferenceAdjunction p q v a hv).counitHom :=
  (laxDifferenceAdjunction p q v a hv).counitHom_isIso_of_postcompFullyFaithful
    (laxDifferenceRho_postcomp_fullyFaithful p q v hv E.obj).toHoFullyFaithful

lemma laxDifferenceAdjunction_counit_isIso :
    IsIso (laxDifferenceAdjunction p q v a hv).counit := by
  have := laxDifferenceAdjunction_counitHom_isIso p q v a hv
  exact counit_isIso_of_counitHom _

include a hv in
lemma laxDifference_isLocalization :
    IsLocalization (laxDifference p q) (invertedEdges (laxDifference p q)) := by
  have := laxDifferenceAdjunction_counit_isIso p q v a hv
  exact AdjointLocalization.isLocalization (laxDifferenceAdjunction p q v a hv)

include a hv in
/-- 通常 pullback から元の lax pullback、差の項 E への実 Verdier 列。 -/
lemma laxDifference_isVerdier :
    IsVerdierSequence (pullbackInclusion p q) (exactLaxDifference p q) where
  fullyFaithful := pullbackInclusion_fullyFaithful p q
  kernel := exactLaxDifference_kernel p q
  quotient := by
    rw [← invertedEdges_eq_cofiber_kernel (pullbackInclusion p q)
      (exactLaxDifference p q) (exactLaxDifference_kernel p q)]
    exact laxDifference_isLocalization p q v a hv

def tammeVerdierSequence : VerdierSequence.{u} where
  left := pullbackCategory p q
  middle := laxCategory p q
  right := E
  inclusion := pullbackInclusion p q
  projection := exactLaxDifference p q
  isVerdier := laxDifference_isVerdier p q v a hv

include a hv in
/-- 任意の標的の実関手 ∞ 圏での商の普遍性。 -/
lemma laxDifference_quotient_universal (T : SSet.{u}) [Quasicategory T] :
    IsQCatEquivalence (localizationPrecomposition (laxDifference p q)
      (cofiberLocalizingEdges (essentialImage (pullbackInclusion p q)))
      (laxDifference_isVerdier p q v a hv).inverts T) :=
  (laxDifference_isVerdier p q v a hv).universal T

end SerrePositivity.KST.LocalizingInvariants
