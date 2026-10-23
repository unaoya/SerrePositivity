module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceDComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition

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
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (v : E.obj ⟶ D.obj)

/-- 元の lax pullback に値を持つ関手 ρ = fromD ∘ v。 -/
def laxDifferenceRho : E.obj ⟶ (laxCategory p q).obj := v ≫ LaxInclusion.fromD p q

lemma laxDifferenceRho_snd : laxDifferenceRho p q v ≫ (laxSnd p q).hom = v := by
  rw [laxDifferenceRho, Category.assoc, LaxInclusion.fromD_snd, Category.comp_id]

lemma laxDifferenceRho_fullyFaithful (hv : IsFullyFaithful v) :
    IsFullyFaithful (laxDifferenceRho p q v) :=
  hv.comp (LaxInclusion.fromD_fullyFaithful p q)

lemma laxDifferenceRho_postcomp_fullyFaithful (hv : IsFullyFaithful v) (A : SSet.{u}) :
    IsFullyFaithful ((ihom A).map (laxDifferenceRho p q v)) :=
  (laxDifferenceRho_fullyFaithful p q v hv).postcompose A

/-- q の可逆余単位を、頂点ごとの可逆性を仮定せず実関手圏で得る。 -/
lemma fullyFaithfulRightAdjunction_counitHom_isIso (a : QCatAdjunction q.hom v)
    (hv : IsFullyFaithful v) : IsIso a.counitHom :=
  a.counitHom_isIso_of_postcompFullyFaithful (hv.postcompose E.obj).toHoFullyFaithful

/-- ρ に差の関手を続けた合成は恒等関手と実関手同型になる。 -/
def laxDifferenceRho_sectionIso (a : QCatAdjunction q.hom v) (hv : IsFullyFaithful v) :
    FunctorIso (laxDifferenceRho p q v ≫ laxDifference p q) (𝟙 E.obj) := by
  have := fullyFaithfulRightAdjunction_counitHom_isIso q v a hv
  have h := FunctorIso.precomp (fromD_differenceIso p q) v
  exact (by simpa only [laxDifferenceRho, Category.assoc] using h) ≪≫ asIso a.counitHom

end SerrePositivity.KST.LocalizingInvariants
