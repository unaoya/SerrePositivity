module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgFullLocalizationSource
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgExtensionSourceComparison
public import SerrePositivity.EInfinity.BarrattEccles.Theory.LocalizedNerveNatTrans
public import SerrePositivity.InfinityCategories.HTT.Section5_2_5.Adjunction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalenceAdjunction

/-!
# 底変更随伴を降ろす二つの比較

## 概要
HA §3.2.2 の導来係数変更を、同じ厳密な代数の随伴と比較する。

## 方針
左は厳密な拡大に向かう augmentation、右は厳密な制限との自然同型を使う。

## 規約
Hom の宇宙だけを上げ、厳密代数と局所化の値は既存のまま使う。

## 使われ方
M13 の導来底変更随伴。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Bicategory SSet MonoidalClosed
open SerrePositivity.InfinityCategories
open scoped Simplicial

local instance adjunctionComparisonHomCategory (X Y : SSet.QCat.{u + 1}) :
    Category.{u + 1} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

local notation "Q[" A "]" => allAlgebraCAlgSource A
local notation "P[" A "]" => allAlgebraDKReplacement A
local notation "I[" A "]" => allAlgebraDKInclusion A
/-- 全代数 nerve から Hom の宇宙を下げる。 -/
abbrev allAlgebraDownNerve (A : Type u) [CommRing A] :
    nerve (allAlgebraRelativeCategory A).category ⟶ nerve (operad A).Algebra :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down ((operad A).Algebra)

/-- Hom の宇宙を上げた全代数の間の厳密な係数拡大。 -/
abbrev allAlgebraCoefficientExtension :
    (allAlgebraRelativeCategory S).category ⥤ (allAlgebraRelativeCategory T).category :=
  allAlgebraDKDown S ⋙ coefficientExtension f ⋙ allAlgebraDKUp T

/-- Hom の宇宙を上げた全代数の間の厳密な係数制限。 -/
abbrev allAlgebraCoefficientRestriction :
    (allAlgebraRelativeCategory T).category ⥤ (allAlgebraRelativeCategory S).category :=
  allAlgebraDKDown T ⋙ coefficientRestriction f ⋙ allAlgebraDKUp S

/-- 全代数の通常の随伴を同じ Hom の宇宙で読む。 -/
def allAlgebraCoefficientAdjunction :
    allAlgebraCoefficientExtension f ⊣ allAlgebraCoefficientRestriction f := by
  let eS : (operad S).Algebra ≌ ULiftHom.{u + 1} (operad S).Algebra := ULiftHom.equiv
  let eT : (operad T).Algebra ≌ ULiftHom.{u + 1} (operad T).Algebra := ULiftHom.equiv
  exact CategoryTheory.Adjunction.comp
    (CategoryTheory.Adjunction.comp eS.symm.toAdjunction (coefficientAlgebraAdjunction f))
    eT.toAdjunction

/-- 全代数の nerve の間の元の随伴。 -/
def allAlgebraCoefficientNerveAdjunction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (nerveMap (allAlgebraCoefficientExtension f))
      (nerveMap (allAlgebraCoefficientRestriction f)) :=
  _root_.SerrePositivity.InfinityCategories.HTT.Section5_2_5.nerveAdjunctionOfAdjunction (allAlgebraCoefficientAdjunction f)

/-- 全相対圏の源と元の厳密代数の源は Hom の変更に関して可換。 -/
lemma allAlgebraCAlgSource_down (A : Type u) [CommRing A] :
    Q[A] = allAlgebraDownNerve A ≫ algebraCAlgSource A := rfl

/-- 全代数の局所化源の上で、導来制限は厳密制限と自然同型。 -/
def allAlgebraCoefficientRestriction_sourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Q[T] ≫ barrattEcclesRestrict f)
      (nerveMap (allAlgebraCoefficientRestriction f) ≫ Q[S]) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((barrattEcclesRestrict_sourceIso f).precomp (allAlgebraDownNerve T)) rfl rfl

/-- 全代数の局所化源の上で、導来拡大は cofibrant 置換後の厳密拡大と自然同型。 -/
def allAlgebraCoefficientExtension_sourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Q[S] ≫ barrattEcclesBaseChange f)
      (nerveMap (P[S] ⋙ I[S] ⋙ allAlgebraCoefficientExtension f) ≫ Q[T]) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((barrattEcclesBaseChange_sourceIso f).precomp (allAlgebraDownNerve S)) rfl rfl

/-- 左導来関手の、全代数上の元の厳密拡大への比較二胞体。 -/
def allAlgebraCoefficientExtension_comparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (Q[S]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (barrattEcclesBaseChange f) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap (allAlgebraCoefficientExtension f)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (Q[T]) := by
  let F := allAlgebraCoefficientExtension f
  let e := allAlgebraCoefficientExtension_sourceIso f
  let η : P[S] ⋙ I[S] ⋙ F ⟶ F :=
    Functor.whiskerRight (allAlgebraDKReplacementAugmentation S) F
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso e).hom ≫ qcatNerveNatTrans η ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (Q[T])

/-- cofibrant 代数の包含を全代数の源に合成すると元の局所化源と同型。 -/
def allAlgebraCAlgSource_cofibrantIso (A : Type u) [CommRing A] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (I[A]) ≫ Q[A]) (cAlgLocalizationSource A) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (cAlgLocalizationSource_algebraIso A) rfl rfl

end SerrePositivity.EInfinity.BarrattEccles
