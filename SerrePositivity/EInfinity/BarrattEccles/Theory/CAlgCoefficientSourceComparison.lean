module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientRestriction
public import SerrePositivity.EInfinity.SimplicialLocalization.WeakNerveInverts
public import SerrePositivity.InfinityCategories.F1B.Localization.UniversalConsequences
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramRestriction

/-!
# 代数の係数変更に使う局所化源の比較

## 概要
HA §3.2.2 の係数変更の比較を、元の局所化源で検証する。

## 方針
cofibrant 代数をもう一度置換しても、augmentation を反転すれば同じ全関手を得る。

## 規約
DK 入力の Hom の宇宙と元の局所化を使う。

## 使われ方
M13 の係数変更と忘却、恒等、合成の自然比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory SSet MonoidalClosed
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- cofibrant 入力の再置換から恒等関手への augmentation。 -/
def cofibrantAlgebraDKReplacementAugmentation :
    cofibrantAlgebraDKInclusion A ⋙ cofibrantAlgebraDKReplacement A ⟶
      𝟭 (cofibrantAlgebraRelativeCategory A).category where
  app X := ULift.up (ObjectProperty.homMk
    ((framedLimitProbeComparisonNatTrans A).app ((cofibrantAlgebraDKInclusion A).obj X)))
  naturality X Y g := by
    apply ULift.ext
    apply ObjectProperty.hom_ext
    exact (framedLimitProbeComparisonNatTrans A).naturality
      ((cofibrantAlgebraDKInclusion A).map g)

set_option maxHeartbeats 800000 in
-- DK 入力の再置換と、その辺の全単体表示を同時に照合する。
/-- cofibrant 入力で再置換して局所化しても、元の局所化源と自然同型。 -/
def cAlgLocalizationSource_algebraIso :
    FunctorIso (cofibrantAlgebraInclusionNerve A ≫ algebraCAlgSource A)
      (cAlgLocalizationSource A) := by
  let D := (cofibrantAlgebraRelativeCategory A).category
  let η := cofibrantAlgebraDKReplacementAugmentation A
  let H := F1B.nerveNatTransHomotopy η
  let P := HomotopyClasses.postHomotopy (cAlgLocalizationSource A) H
  have hp (z : (nerve D) _⦋0⦌) :
      IsInvertibleEdge (simplicialHomotopyVertexEdge P z).toTruncated := by
    obtain ⟨X, rfl⟩ := ComposableArrows.mk₀_surjective z
    have hq : (cofibrantAlgebraRelativeCategory A).weakEquivalences (η.app X) := by
      apply (cofibrantAlgebraRelativeCategory_weakEquivalences_iff A _).mpr
      exact framedLimitProbeComparison_quasiIso A ((cofibrantAlgebraDKInclusion A).obj X)
    exact (isInvertibleEdge_congr
      (e := (simplicialHomotopyVertexEdge P (nerveVertex X)).toTruncated)
      (f := ((nerve.edgeMk (η.app X)).map (cAlgLocalizationSource A)).toTruncated)
      (congrArg ((cAlgLocalizationSource A).app (Opposite.op ⦋1⦌))
        (F1B.nerveNatTransHomotopy_component η X))).mpr
      (SimplicialLocalization.weakNerveEdges_inverts_arrows
        (cofibrantAlgebraRelativeCategory A) _ (cAlgLocalizationSource_inverts A) _ hq)
  apply F2.functorIsoOfEq (functorIsoOfPointwiseInvertibleHomotopy P hp)
  · rw [algebraCAlgSource, ← Category.assoc]
    congr 1
  · rw [show nerveMap (𝟭 D) = 𝟙 (nerve D) from nerveFunctor.map_id (Cat.of D),
      Category.id_comp]

/-- 局所化源上で検証した自然同型を、既存の CAlg 上へ降ろす。 -/
def cAlgLocalizationSource_descendIso {Y : SSet.{u + 1}} [Quasicategory Y]
    {F G : CAlg_R A ⟶ Y}
    (e : FunctorIso (cAlgLocalizationSource A ≫ F) (cAlgLocalizationSource A ≫ G)) :
    FunctorIso F G := by
  let q := cAlgLocalizationSource A
  let ff := ((cAlgLocalizationSource_isLocalization A).precomposition_isFullyFaithful Y)
    |>.toHoFullyFaithful
  apply ff.preimageIso
  change VertexIso (((pre q).app Y).app (Opposite.op ⦋0⦌) (functorVertex F))
    (((pre q).app Y).app (Opposite.op ⦋0⦌) (functorVertex G))
  rw [functorVertex_precomposition, functorVertex_precomposition]
  exact e

/-- 全代数上で検証した比較は、cofibrant 入力を介して降ろせる。 -/
def algebraCAlgSource_descendIso {Y : SSet.{u + 1}} [Quasicategory Y]
    {F G : CAlg_R A ⟶ Y}
    (e : FunctorIso (algebraCAlgSource A ≫ F) (algebraCAlgSource A ≫ G)) :
    FunctorIso F G := by
  apply cAlgLocalizationSource_descendIso A
  let c := cAlgLocalizationSource_algebraIso A
  exact (c.postcomp F).symm ≪≫
    (by simpa only [Category.assoc] using e.precomp (cofibrantAlgebraInclusionNerve A)) ≪≫
      c.postcomp G

end SerrePositivity.EInfinity.BarrattEccles
