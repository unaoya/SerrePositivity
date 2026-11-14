module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.LaxDifferenceRho

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceDComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：q の充満忠実な右随伴から、差の右随伴候補 ρ と実際の切断同型を構成する。
方針：元の D 包含との合成を使い、差と D 包含の比較と q の実随伴余単位を合成。
規約：切断同型だけから随伴性を主張しない。使われ方：差の局所化の実右随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj)

/-- 元の lax pullback に値を持つ関手 ρ = fromD ∘ v。 -/
def laxDifferenceRho : E.obj ⟶ (laxCategory p q).obj := v ≫ LaxInclusion.fromD p q

lemma laxDifferenceRho_snd : laxDifferenceRho p q v ≫ (laxSnd p q).hom = v := by
  rw [laxDifferenceRho, Category.assoc, LaxInclusion.fromD_snd, Category.comp_id]

lemma laxDifferenceRho_fullyFaithful (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (laxDifferenceRho p q v) :=
  hv.comp (LaxInclusion.fromD_fullyFaithful p q)

lemma laxDifferenceRho_postcomp_fullyFaithful (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v) (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((ihom A).map (laxDifferenceRho p q v)) :=
  (laxDifferenceRho_fullyFaithful p q v hv).postcompose A

/-- ρ に差の関手を続けた合成は恒等関手と実関手同型になる。 -/
def laxDifferenceRho_sectionIso (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (laxDifferenceRho p q v ≫ laxDifference p q) (𝟙 E.obj) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.fullyFaithfulRightAdjunction_counitHom_isIso q v a hv
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (fromD_differenceIso p q) v
  exact (by simpa only [laxDifferenceRho, Category.assoc] using h) ≪≫ asIso a.counitHom

end SerrePositivity.KST.LocalizingInvariants

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Eq (6)"] _root_.SerrePositivity.KST.LocalizingInvariants.laxDifferenceRho_sectionIso
attribute [cite Tamme "Prop 11"] _root_.SerrePositivity.KST.LocalizingInvariants.laxDifferenceRho_fullyFaithful
