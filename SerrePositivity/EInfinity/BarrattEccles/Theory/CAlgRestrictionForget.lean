module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientSourceComparison
public import SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedRestrictionSource
public import SerrePositivity.EInfinity.BarrattEccles.CAlgUnderlyingDerivedComparison

/-!
# 導来代数の係数制限と忘却

## 概要
HA §3.2.2 の係数制限は、忘却した複体の係数制限に自然に一致する。

## 方針
元の厳密代数全体で比較し、局所化源の充満忠実性を使う。

## 規約
W16 の導来係数制限と既存の忘却を使う。

## 使われ方
M13 の `restrict_forget` 欄。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory SSet DifferentialGraded
open SerrePositivity.InfinityCategories
open scoped Simplicial

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 導来係数制限の忘却は、忘却した導来複体の係数制限と自然同型。 -/
def barrattEcclesRestrict_forget :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (barrattEcclesRestrict f ≫ cAlgForgetDerived S)
      (cAlgForgetDerived T ≫ ComplexLimits.barrattEcclesRestrictD f) := by
  apply algebraCAlgSource_descendIso T
  let R := ComplexLimits.barrattEcclesRestrictD f
  let N := nerveMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad T))
  let K := nerveMap (ScalarExtension.restriction f)
  let Q := _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource S
  let r := nerveMap (coefficientRestriction f)
  have e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (algebraCAlgSource T ≫ barrattEcclesRestrict f ≫ cAlgForgetDerived S)
      (r ≫ algebraCAlgSource S ≫ cAlgForgetDerived S) := by
    simpa only [Category.assoc] using
      (barrattEcclesRestrict_sourceIso f).postcomp (cAlgForgetDerived S)
  have e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (r ≫ algebraCAlgSource S ≫ cAlgForgetDerived S) (N ≫ K ≫ Q) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((algebraCAlgSource_underlyingDerivedIso S).precomp r) rfl rfl
  have e₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (N ≫ K ≫ Q) (algebraUnderlyingDerivedSource T ≫ R) := by
    simpa only [algebraUnderlyingDerivedSource, Category.assoc] using
      ((ComplexLimits.barrattEcclesRestrictD_sourceIso f).precomp N).symm
  have e₄ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (algebraUnderlyingDerivedSource T ≫ R)
      (algebraCAlgSource T ≫ cAlgForgetDerived T ≫ R) := by
    simpa only [Category.assoc] using
      ((algebraCAlgSource_underlyingDerivedIso T).postcomp R).symm
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

end SerrePositivity.EInfinity.BarrattEccles
