module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisIdentityNuSquare
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisNuComparison

/-!
概要：中央射と同じ逆回転基底の実右面を、native nerve と固定 ν で比較する。
方針：同じ全 cone 像小模型の前三角性・完備性と元 dg 二辺の ν 自然性を使う。
規約：元恒等二脚への D2 全比較と列認証は別工程。
使われ方：同じ S 長方形の右面の頂点・二境界を指定する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "L" => DGOdotMilnorRightAxisTarget R d
local notation "D" => DGOdotMilnorRightAxisIdentityDifference R d
local notation "F" => dgHomGluingConeFunctor R (U) (U) (U)
  (DGFunctor.id (U)) (DGFunctor.id (U))

/-- 概要：同じ実 cone 全像小模型の前三角性。
方針：同じ指定族を持つ包絡の定理を適用する。
規約：元の cone を保持。使われ方：native 差の完全性。 -/
lemma dgOdotMilnorRightAxisIdentityDifference_pretriangulated :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (D) :=
  dgSmallPerfectEnvelope_pretriangulated R (U) (L) (F).obj

/-- 概要：同じ実 cone 全像小模型の coherent 完備性。
方針：同じ包絡の実 Perf 評価同値を使用する。
規約：元の像を選び直さない。使われ方：固定 ν 終域の比較。 -/
lemma dgOdotMilnorRightAxisIdentityDifference_complete :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (D)) :=
  dgSmallPerfectEnvelope_complete R (U) (L) (F).obj

/-- 概要：同じ逆回転基底の native／固定 ν 指定同値。
方針：元基底の前三角性と完備性を使用する。
規約：同じ実 S 頂点。使われ方：右面の対角始域比較。 -/
def dgOdotMilnorRightAxisIdentityBaseNativeValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U))
    (dgKInputStableValue R (dgOdotMilnorRightAxisIdentityBaseInput R d)).obj :=
  (@dgKNativeValueComparison_isQCatEquivalence R _ (U) _ _
    (dgOdotMilnorRightAxisBase_pretriangulated R d)
    (dgOdotMilnorRightAxisBase_complete R d)).choose

/-- 概要：同じ全 cone 像の native／固定 ν 指定同値。
方針：元の実像模型の前三角性と完備性を使用する。
規約：同じ実 S 頂点。使われ方：右面の差終域比較。 -/
def dgOdotMilnorRightAxisIdentityDifferenceNativeValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (D))
    (dgKInputStableValue R (dgOdotMilnorRightAxisIdentityDifferenceInput R d)).obj :=
  (@dgKNativeValueComparison_isQCatEquivalence R _ (D) _ _
    (dgOdotMilnorRightAxisIdentityDifference_pretriangulated R d)
    (dgOdotMilnorRightAxisIdentityDifference_complete R d)).choose

/-- 概要：同じ strict 対角の native／固定 ν 全比較。
方針：元の二頂点比較に同じ実 dg 対角の自然性を適用する。
規約：中央終域は保存済み中央射と同じ。使われ方：共有辺の全比較。 -/
def dgOdotMilnorRightAxisIdentityDiagonalNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorRightAxisIdentityBaseNativeValueEquivalence R d).hom ≫
      (dgKInputNuMap R (dgOdotMilnorRightAxisIdentityDiagonalInputMap R d)).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisIdentityDiagonal R d) ≫
      (dgOdotMilnorRightAxisTargetNativeValueEquivalence R d).hom) :=
  @dgKNativeNuNaturality R _ (U) (L) _ _
    (dgOdotMilnorRightAxisBase_pretriangulated R d) _ _
    (dgOdotMilnorRightAxisTarget_pretriangulated R d)
    (dgOdotMilnorRightAxisIdentityDiagonal R d)

/-- 概要：同じ実 cone 差の native／固定 ν 全比較。
方針：元の実 Hom 作用を保って同じ自然性を適用する。
規約：D2 の普遍差比較とは区別。使われ方：右面の差境界の指定比較。 -/
def dgOdotMilnorRightAxisIdentityDifferenceNuComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorRightAxisTargetNativeValueEquivalence R d).hom ≫
      (dgKInputNuMap R (dgOdotMilnorRightAxisIdentityDifferenceInputMap R d)).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisIdentityDifference R d) ≫
      (dgOdotMilnorRightAxisIdentityDifferenceNativeValueEquivalence R d).hom) :=
  @dgKNativeNuNaturality R _ (L) (D) _ _
    (dgOdotMilnorRightAxisTarget_pretriangulated R d) _ _
    (dgOdotMilnorRightAxisIdentityDifference_pretriangulated R d)
    (dgOdotMilnorRightAxisIdentityDifference R d)

/-- 概要：実 cone 全像の固定 ν 終域を同じ逆回転基底値へ戻す指定同値。
方針：同じ全像包含の Perf 評価と同じ基底の固定値比較を合成する。
規約：cone 像対象を選び直さない。使われ方：恒等普遍差の終域照合。 -/
def dgOdotMilnorRightAxisIdentityDifferenceValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorRightAxisIdentityDifferenceInput R d)).obj
    (dgKInputStableValue R (dgOdotMilnorRightAxisIdentityBaseInput R d)).obj :=
  (dgOdotMilnorRightAxisIdentityDifferenceNativeValueEquivalence R d).symm.trans
    ((dgSmallPerfectEnvelopeNerveEquivalence R (U) (L) (F).obj).trans
      (dgKNativePerfectValueEquivalence R (U)))

/-- 概要：同じ終域同値は元の実 cone 全像評価を全関手同型で回収する。
方針：元 native／ν 指定同値の単位を同じ評価で後合成する。
規約：全 Hom 作用を保持。使われ方：D2 全 cone 比較の終域固定。 -/
def dgOdotMilnorRightAxisIdentityDifferenceValueEquivalence_native : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorRightAxisIdentityDifferenceNativeValueEquivalence R d).hom ≫
      (dgOdotMilnorRightAxisIdentityDifferenceValueEquivalence R d).hom)
    ((dgSmallPerfectEnvelopeNerveEquivalence R (U) (L) (F).obj).hom ≫
      (dgKNativePerfectValueEquivalence R (U)).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((dgOdotMilnorRightAxisIdentityDifferenceNativeValueEquivalence R d).homInvIso.postcomp
      ((dgSmallPerfectEnvelopeNerveEquivalence R (U) (L) (F).obj).hom ≫
        (dgKNativePerfectValueEquivalence R (U)).hom))
    (Category.assoc _ _ _) (Category.id_comp _)

end SerrePositivity.KST.SConstruction
