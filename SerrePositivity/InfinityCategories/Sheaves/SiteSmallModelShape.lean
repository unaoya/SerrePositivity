module

public import SerrePositivity.InfinityCategories.Sheaves.CechShapeCofinality
public import SerrePositivity.InfinityCategories.Sheaves.GlobalSections
public import SerrePositivity.InfinityCategories.Sheaves.SiteReindex
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitExistence
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
概要：大きい site の元の nerve と小さい模型の持ち上げた nerve を、同じ係数の宇宙で比較する。
方針：既存の二つの nerve–AsSmall の同型と通常圏の同値を合成する。
使われ方：HTT 1.2.7.3、Kerodon §4.5.1（Tag 01DQ）の本質的に小さい site の前層圏。
規約：対象は Type(u+1)、射は Type u、係数は SSet(u+1)。係数の宇宙を上げず、κを新設しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type (u + 1)} [Category.{u} C] {D : Type u} [SmallCategory D]

/-- 小さい模型との同値から、係数の宇宙を変えない元の反対 nerve の同値を作る。 -/
def siteSmallModelShapeEquivalence (e : D ≌ C) :
    QCatEquivalence (presheafShape D) (nerve Cᵒᵖ) := by
  let a : Dᵒᵖ ≌ AsSmall.{u + 1} Dᵒᵖ := AsSmall.equiv
  let b : Cᵒᵖ ≌ AsSmall.{u + 1} Cᵒᵖ := AsSmall.equiv
  let q := a.symm.trans (e.op.trans b)
  exact (qCatEquivalenceOfIso (nerveAsSmallIso.{u, u + 1} Dᵒᵖ)).trans
    ((nerveQCatEquivalence q).trans (qCatEquivalenceOfIso (nerveAsSmallMaxIso Cᵒᵖ).symm))

/-- 同じ形状の順射の全単体での式。対象だけの比較ではない。 -/
lemma siteSmallModelShapeEquivalence_hom_app (e : D ≌ C) {n : ℕ}
    (σ : (presheafShape D) _⦋n⦌) :
    (siteSmallModelShapeEquivalence e).hom.app _ σ = σ.down ⋙ e.functor.op := rfl

/-- 大きい site の元の全前層を、同じ係数の小さい模型の前層へ再添字する。 -/
def reindexSmallModelPresheafFunctor (e : D ≌ C) (E : SSet.{u + 1}) :
    (ihom (nerve Cᵒᵖ)).obj E ⟶ PresheafCat D E :=
  (pre (siteSmallModelShapeEquivalence e).hom).app E

/-- 同じ係数のまま、全前層圏の再添字は同値である。 -/
lemma reindexSmallModelPresheafFunctor_isQCatEquivalence (e : D ≌ C)
    {E : SSet.{u + 1}} [Quasicategory E] :
    IsQCatEquivalence (reindexSmallModelPresheafFunctor e E) :=
  (siteSmallModelShapeEquivalence e).isQCatEquivalence.isPrecompositionEquivalence E

/-- 小さい模型の極限から、元の大きい site の任意の前層の極限を同じ係数で回収する。 -/
lemma hasLimit_largePresheaf_of_smallModel (e : D ≌ C)
    {E : SSet.{u + 1}} [Quasicategory E]
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : nerve Cᵒᵖ ⟶ E) : HasLimit F :=
  hasLimit_of_equivalentRestriction (siteSmallModelShapeEquivalence e).hom
    (siteSmallModelShapeEquivalence e).isQCatEquivalence F (hasLimit_presheaf hE _)

/-- Mathlib の元の本質的小ささの入力から、同じ宇宙での形状同値を得る。 -/
def essentiallySmallSiteShapeEquivalence (C : Type (u + 1)) [Category.{u} C]
    [EssentiallySmall.{u} C] :
    QCatEquivalence (presheafShape (SmallModel.{u} C)) (nerve Cᵒᵖ) :=
  siteSmallModelShapeEquivalence (equivSmallModel C).symm

end SerrePositivity.InfinityCategories.Sheaves
