module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientExtension
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientSourceComparison
public import SerrePositivity.EInfinity.BarrattEccles.CAlgForgetDerived
public import SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedExtensionSource

/-!
# 導来代数の係数拡大と忘却の比較の降下

## 概要
HA §3.2.2 の係数拡大の比較を、同じ厳密な cofibrant 源から降ろす。

## 方針
厳密な底変更の台を項別の底変更と同定し、導来複体側の比較を合成する。

## 規約
厳密な局所化源は構成済みの模型のものを使う。

## 使われ方
M13 の `baseChange_forget` 欄の局所化による還元。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory DifferentialGraded SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 厳密な係数拡大と cofibrant 代数の台を取る操作は項別係数拡大と可換。 -/
lemma cofibrantAlgebraCoefficientExtension_forgetNerve :
    nerveMap (cofibrantAlgebraDKCoefficientExtension f) ≫ cofibrantAlgebraForgetNerve T =
      cofibrantAlgebraForgetNerve S ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change (Γ ⋙ cofibrantAlgebraDKCoefficientExtension f) ⋙ cofibrantAlgebraDKForget T =
    (Γ ⋙ cofibrantAlgebraDKForget S) ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f
  rfl

/-- M13 の比較は、cofibrant 源における複体の導来係数拡大と項別係数拡大の比較に還元する。 -/
def barrattEcclesBaseChange_forget_of_sourceIso
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (cofibrantAlgebraForgetNerve S ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f) ≫
        ComplexLimits.complexOrdinaryDerivedSource T)
      (cofibrantAlgebraUnderlyingDerivedSource S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (barrattEcclesBaseChange f ≫ cAlgForgetDerived T)
      (cAlgForgetDerived S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f) := by
  apply cAlgLocalizationSource_descendIso S
  let L := nerveMap (cofibrantAlgebraDKCoefficientExtension f)
  let U := cofibrantAlgebraForgetNerve S
  let B := nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f)
  let Q := ComplexLimits.complexOrdinaryDerivedSource T
  have e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (cAlgLocalizationSource S ≫ barrattEcclesBaseChange f ≫ cAlgForgetDerived T)
      (L ≫ cAlgLocalizationSource T ≫ cAlgForgetDerived T) := by
    simpa only [Category.assoc] using
      (barrattEcclesBaseChange_cofibrantIso f).postcomp (cAlgForgetDerived T)
  have e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ cAlgLocalizationSource T ≫ cAlgForgetDerived T)
      (U ≫ B ≫ Q) := by
    refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((cAlgForgetDerived_sourceIso T).precomp L) rfl ?_
    rw [cofibrantAlgebraUnderlyingDerivedSource, ← Category.assoc,
      cofibrantAlgebraCoefficientExtension_forgetNerve f, Category.assoc]
  have e₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (cofibrantAlgebraUnderlyingDerivedSource S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f)
      (cAlgLocalizationSource S ≫ cAlgForgetDerived S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f) := by
    simpa only [Category.assoc] using
      ((cAlgForgetDerived_sourceIso S).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f)).symm
  exact e₁ ≪≫ e₂ ≪≫ e ≪≫ e₃

/-- HA §3.2.2 の比較を、cofibrant 代数の台の K 平坦性に還元する。 -/
def barrattEcclesBaseChange_forget_of_cofibrantCarrierKFlat
    (h : ∀ X : (cofibrantAlgebraRelativeCategory S).category,
      complexKFlat S ((cofibrantAlgebraDKForget S).obj X)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (barrattEcclesBaseChange f ≫ cAlgForgetDerived T)
      (cAlgForgetDerived S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f) := by
  apply barrattEcclesBaseChange_forget_of_sourceIso f
  have hF (x : (nerve (cofibrantAlgebraRelativeCategory S).category) _⦋0⦌) :
      complexKFlat S ((atVertex (cofibrantAlgebraForgetNerve S) x).obj 0) := by
    obtain ⟨X, rfl⟩ := ComposableArrows.mk₀_surjective x
    exact h X
  simpa only [cofibrantAlgebraUnderlyingDerivedSource, Category.assoc] using
    (ComplexLimits.derivedInfinityBaseChange_sourceIso f (cofibrantAlgebraForgetNerve S) hF).symm

end SerrePositivity.EInfinity.BarrattEccles
