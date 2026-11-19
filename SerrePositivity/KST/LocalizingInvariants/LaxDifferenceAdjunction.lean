module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceMapping
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveMappingAdjunction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.AdjointVerdier

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v)

/-- 元の差の関手の右随伴は、元の D 包含と v の合成。 -/
def laxDifferenceAdjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (laxDifference p q) (laxDifferenceRho p q v) :=
  adjunctionOfReflectiveMapping (laxDifferenceRho_sectionIso p q v a hv)
    (laxDifferenceMapping_equivalence p q v a hv)

lemma laxDifferenceAdjunction_counitHom_isIso :
    IsIso (laxDifferenceAdjunction p q v a hv).counitHom :=
  (laxDifferenceAdjunction p q v a hv).counitHom_isIso_of_postcompFullyFaithful
    (laxDifferenceRho_postcomp_fullyFaithful p q v hv E.obj).toHoFullyFaithful

lemma laxDifferenceAdjunction_counit_isIso :
    IsIso (laxDifferenceAdjunction p q v a hv).counit := by
  have := laxDifferenceAdjunction_counitHom_isIso p q v a hv
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.counit_isIso_of_counitHom _

include a hv in
lemma laxDifference_isLocalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (laxDifference p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (laxDifference p q)) := by
  have := laxDifferenceAdjunction_counit_isIso p q v a hv
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization (laxDifferenceAdjunction p q v a hv)

include a hv in
/-- 通常 pullback から元の lax pullback、差の項 E への実 Verdier 列。 -/
lemma laxDifference_isVerdier :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (pullbackInclusion p q) (exactLaxDifference p q) where
  fullyFaithful := pullbackInclusion_fullyFaithful p q
  kernel := exactLaxDifference_kernel p q
  quotient := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.invertedEdges_eq_cofiber_kernel (pullbackInclusion p q)
      (exactLaxDifference p q) (exactLaxDifference_kernel p q)]
    exact laxDifference_isLocalization p q v a hv

def tammeVerdierSequence : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u} where
  left := pullbackCategory p q
  middle := laxCategory p q
  right := E
  inclusion := pullbackInclusion p q
  projection := exactLaxDifference p q
  isVerdier := laxDifference_isVerdier p q v a hv

include a hv in
/-- 任意の標的の実関手 ∞ 圏での商の普遍性。 -/
lemma laxDifference_quotient_universal (T : SSet.{u}) [Quasicategory T] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (laxDifference p q)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q)))
      (laxDifference_isVerdier p q v a hv).inverts T) :=
  (laxDifference_isVerdier p q v a hv).universal T

end SerrePositivity.KST.LocalizingInvariants

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Lemma 1.12" (partial := component) "仮定：一方の脚に充満忠実な右随伴を持つ安定 lax の提示（Lean が強い）。結論：差関手の右随伴による局所化。Ind 上で p を一般に Bousfield 局所化とし cofib(is→id) を同定する主張は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.laxDifference_isLocalization
attribute [cite Tamme "Cor 12" (partial := component) "仮定：安定圏の完全な二脚と右脚の充満忠実な右随伴（Lean は表示可能性を仮定しない）。結論：通常の引き戻しから lax 引き戻しを経て余ファイバー先に至る実 Verdier 列（原典の同じ四頂点での核と商。Pr^L の列としての記述は含まない）。"] _root_.SerrePositivity.KST.LocalizingInvariants.laxDifference_isVerdier
attribute [cite Tamme "Eq (11)" (partial := stronger-hyp) "仮定：小安定圏上ですでに引き戻しで右脚に充満忠実な右随伴がある（Lean が強い：右随伴を Ind 上から小圏へ制限できる場合）。結論：指定の通常の引き戻しから lax 引き戻しを経る完全列（原典と同じ核と商）。"] _root_.SerrePositivity.KST.LocalizingInvariants.laxDifference_isVerdier
attribute [cite Tamme "Eq (11)" (partial := stronger-hyp) "仮定：小安定圏上ですでに引き戻しで右脚に充満忠実な右随伴がある（Lean が強い：右随伴を Ind 上から小圏へ制限できる場合）。結論：指定の通常の引き戻しから lax 引き戻しを経る完全列（原典と同じ核と商）。"] _root_.SerrePositivity.KST.LocalizingInvariants.tammeVerdierSequence
attribute [cite Tamme "Prop 11"] _root_.SerrePositivity.KST.LocalizingInvariants.laxDifferenceAdjunction
attribute [cite Tamme "Thm 15" (partial := stronger-hyp) "仮定：小安定圏上ですでに引き戻しで右脚に充満忠実な右随伴がある（Lean が強い：右随伴を Ind 上から小圏へ制限できる場合）。結論：指定の通常の引き戻しから lax 引き戻しを経る完全列（原典と同じ核と商）。"] _root_.SerrePositivity.KST.LocalizingInvariants.laxDifference_isVerdier
attribute [cite Tamme "Thm 15" (partial := stronger-hyp) "仮定：小安定圏上ですでに引き戻しで右脚に充満忠実な右随伴がある（Lean が強い：右随伴を Ind 上から小圏へ制限できる場合）。結論：指定の通常の引き戻しから lax 引き戻しを経る完全列（原典と同じ核と商）。"] _root_.SerrePositivity.KST.LocalizingInvariants.tammeVerdierSequence
