module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgAdjunctionComparison
public import SerrePositivity.EInfinity.BarrattEccles.Theory.LocalizedAdjunctionAssembly
public import SerrePositivity.EInfinity.BarrattEccles.Theory.LocalizedAdjunctionWhiskering

/-!
# Barratt–Eccles の導来底変更随伴

## 概要
HA §3.2.2 の拡大と制限の随伴を、同じ CAlg 上に構成する。

## 方針
厳密な随伴を局所化し、左比較は cofibrant 入力上で可逆であることを使う。

## 規約
モデル構造の追加入力を取らず、全関手の単位・余単位を与える。

## 使われ方
M13 の `baseChange_adjunction` 欄。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Bicategory SSet MonoidalClosed SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial

local instance derivedAdjunctionHomCategory (X Y : SSet.QCat.{u + 1}) :
    Category.{u + 1} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

local notation "I[" A "]" => allAlgebraDKInclusion A
local notation "P[" A "]" => allAlgebraDKReplacement A
local notation "Q[" A "]" => allAlgebraCAlgSource A

/-- 置換の augmentation は全代数の局所化で反転される。 -/
lemma allAlgebraDKReplacementAugmentation_isIso (A : Type u) [CommRing A] :
    IsIso (qcatNerveNatTrans (allAlgebraDKReplacementAugmentation A) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (Q[A])) := by
  apply qcatNerveNatTrans_whiskerRight_isIso
  intro X
  apply weakNerveEdges_inverts_arrows (allAlgebraRelativeCategory A) _
    (allAlgebraCAlgSource_isLocalization A).choose
  exact framedLimitProbeComparison_quasiIso A ((allAlgebraDKDown A).obj X)

/-- cofibrant 入力に制限すると左導来拡大の比較は可逆。 -/
lemma allAlgebraCoefficientExtension_comparison_isIso :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap (I[S])) ◁ allAlgebraCoefficientExtension_comparison f) := by
  let F := allAlgebraCoefficientExtension f
  let η : P[S] ⋙ I[S] ⋙ F ⟶ F :=
    Functor.whiskerRight (allAlgebraDKReplacementAugmentation S) F
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap (I[S]))
  have h : IsIso (qcatNerveNatTrans (Functor.whiskerLeft (I[S]) η) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (Q[T])) := by
    apply qcatNerveNatTrans_whiskerRight_isIso
    intro X
    apply weakNerveEdges_inverts_arrows (allAlgebraRelativeCategory T) _
      (allAlgebraCAlgSource_isLocalization T).choose
    let e := (cofibrantAlgebraDKReplacementAugmentation S).app X
    have he : (cofibrantAlgebraRelativeCategory S).weakEquivalences e :=
      framedLimitProbeComparison_quasiIso S ((cofibrantAlgebraDKInclusion S).obj X)
    exact cofibrantAlgebraDKCoefficientExtension_map_weak f e he
  rw [qcatNerveNatTrans_whiskerLeft, qcat_whisker_assoc] at h
  change IsIso (i ◁
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso (allAlgebraCoefficientExtension_sourceIso f)).hom ≫
      qcatNerveNatTrans η ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (Q[T])))
  rw [whiskerLeft_comp]
  exact IsIso.comp_isIso' inferInstance h

/-- cofibrant 入力からの全前合成は充満忠実。 -/
lemma allAlgebraCAlgSource_cofibrant_precomp (A : Type u) [CommRing A]
    (Z : SSet.{u + 1}) [Quasicategory Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (nerveMap (I[A]) ≫ Q[A])).app Z) := by
  exact ((allAlgebraCAlgSource_cofibrantIso A).map_pre Z).isFullyFaithful_iff.mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful (cAlgLocalizationSource_isLocalization A) Z)

/-- HA §3.2.2 の係数拡大と係数制限の導来随伴。 -/
def barrattEcclesBaseChange_adjunction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (barrattEcclesBaseChange f) (barrattEcclesRestrict f) := by
  let a := allAlgebraCoefficientNerveAdjunction f
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (Q[S])
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (Q[T])
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap (I[S]))
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap (P[S]))
  let α := allAlgebraCoefficientExtension_comparison f
  let β := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIsoToQcatIso (allAlgebraCoefficientRestriction_sourceIso f)
  let w : p ≫ i ⟶ 𝟙 _ := qcatNerveNatTrans (allAlgebraDKReplacementAugmentation S)
  letI : IsIso (w ▷ q) := allAlgebraDKReplacementAugmentation_isIso S
  letI : IsIso (i ◁ α) := allAlgebraCoefficientExtension_comparison_isIso f
  exact adjunctionFromLocalization a q r i α β p w
    (qcatPrecompFullyFaithful _ (allAlgebraCAlgSource_cofibrant_precomp S (CAlg_R S)))
    (qcatPrecompFullyFaithful _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful (allAlgebraCAlgSource_isLocalization T) (CAlg_R S)))
    (qcatPrecompFullyFaithful _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful (allAlgebraCAlgSource_isLocalization T) (CAlg_R T)))
    (qcatPrecompFullyFaithful _ (allAlgebraCAlgSource_cofibrant_precomp S (CAlg_R T)))

end SerrePositivity.EInfinity.BarrattEccles
