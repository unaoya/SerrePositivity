module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityNativeComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：恒等右面の基底と実 cone 全像の固定 ν 値を、同じ元商の Perf 値へ照合する。
方針：元小模型の実 Perf 評価と、同じ native／ν 同値を合成する。
規約：実 cone の像対象と元 resolved 商を保持。恒等 lax 差の比較は別工程。
使われ方：実右面の左右頂点と、D2 の全 cone 比較の終域を固定する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "Q" => DGQuotient.QuotientObject (DGCategoryCellResolution.Source R (B))
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "C" => DGOdotMilnorIdentityBase R d
local notation "L" => DGOdotMilnorIdentityGluing R d
local notation "F" => dgHomGluingConeFunctor R (C) (C) (C)
  (DGFunctor.id (C)) (DGFunctor.id (C))
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (C) := dgOdotMilnorIdentityBase_pretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotMilnorIdentityDifference R d) :=
  dgOdotMilnorIdentityDifference_pretriangulated R d

/-- 概要：恒等右面の同じ基底の ν 値と元 resolved 商の ν 値の実同値。
方針：元小 Perf 評価と元商 Perf の固定値比較を使う。
規約：元商の完備性は仮定しない。使われ方：右面の元商頂点の回収。 -/
def dgOdotMilnorIdentityBaseValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)).obj
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)).obj :=
  (dgOdotMilnorIdentityBase_nu_equivalence R d).choose.symm.trans
    ((dgSmallPerfectEnvelopeNerveEquivalence R (Q) Empty (dgSmallPerfectBaseFamily R (Q))).trans
      (dgOdotMilnorResolvedPerfectValueEquivalence R d))

/-- 概要：基底値同値は元 native 小模型の実評価を全関手同型で回収する。
方針：同じ native／ν 同値の単位を実評価で後合成する。
規約：対象別同型へ弱めない。使われ方：右面の対角始域成分の指定。 -/
def dgOdotMilnorIdentityBaseValueEquivalence_native : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R (C) ≫ (dgOdotMilnorIdentityBaseValueEquivalence R d).hom)
    ((dgSmallPerfectEnvelopeNerveEquivalence R (Q) Empty
      (dgSmallPerfectBaseFamily R (Q))).hom ≫
      (dgOdotMilnorResolvedPerfectValueEquivalence R d).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((dgOdotMilnorIdentityBase_nu_equivalence R d).choose.homInvIso.postcomp
      ((dgSmallPerfectEnvelopeNerveEquivalence R (Q) Empty
        (dgSmallPerfectBaseFamily R (Q))).hom ≫
        (dgOdotMilnorResolvedPerfectValueEquivalence R d).hom))
    (Category.assoc _ _ _) (Category.id_comp _)

/-- 概要：実 cone 全像小模型の ν 値と同じ基底の ν 値の実同値。
方針：同じ全像を含む小 Perf 評価と元基底の Perf 値比較を使う。
規約：cone 対象の代表を選び直さない。使われ方：実差の終域照合。 -/
def dgOdotMilnorIdentityDifferenceValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorIdentityDifferenceInput R d)).obj
    (dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)).obj :=
  (dgOdotMilnorIdentityDifference_nu_equivalence R d).choose.symm.trans
    ((dgSmallPerfectEnvelopeNerveEquivalence R (C) (L) (F).obj).trans
      (dgKNativePerfectValueEquivalence R (C)))

/-- 概要：実差の終域同値は元全像の実評価を全関手同型で回収する。
方針：同じ native／ν 同値の単位を元評価で後合成する。
規約：同じ全 Hom 作用を保持。使われ方：D2 の全 cone 比較の指定終域。 -/
def dgOdotMilnorIdentityDifferenceValueEquivalence_native : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R (DGOdotMilnorIdentityDifference R d) ≫
      (dgOdotMilnorIdentityDifferenceValueEquivalence R d).hom)
    ((dgSmallPerfectEnvelopeNerveEquivalence R (C) (L) (F).obj).hom ≫
      (dgKNativePerfectValueEquivalence R (C)).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((dgOdotMilnorIdentityDifference_nu_equivalence R d).choose.homInvIso.postcomp
      ((dgSmallPerfectEnvelopeNerveEquivalence R (C) (L) (F).obj).hom ≫
        (dgKNativePerfectValueEquivalence R (C)).hom))
    (Category.assoc _ _ _) (Category.id_comp _)
end SerrePositivity.KST.SConstruction
