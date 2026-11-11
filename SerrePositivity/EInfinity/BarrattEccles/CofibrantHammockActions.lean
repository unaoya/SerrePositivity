module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantHammockInclusionLaws
public import SerrePositivity.EInfinity.BarrattEccles.SourceFramePrecompose
public import SerrePositivity.EInfinity.Hammock.MixedRelativePointActions

/-!
# 元の cofibrant hammock 包含による前後合成の保存

概要：HomLift を通る既存の包含は元の射による両側の作用を保つ。
方針：全語の正規化式で同じ包含と直接の相対写像を同定する。
規約：元の包含・元の HomLift 同型・元の点と作用を変更しない。
使われ方：実 DK Hom と既存 Map^h の比較の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Hammock
variable (A : Type u) [CommRing A]

lemma cofibrantAlgebraHammockInclusionMap_eq_mixed
    (X Y : (cofibrantAlgebraRelativeCategory A).category) :
    let := modelCategory A
    cofibrantAlgebraHammockInclusionMap A X Y =
      MixedRelative.reducedMap (cofibrantAlgebraDKInclusionRelative A) X Y := by
  let := modelCategory A
  apply (cancel_epi (reducedColimitIso
    (cofibrantAlgebraRelativeCategory A).weakEquivalences X Y).hom).1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_hom_ext
  intro w
  rw [← Category.assoc, reducedColimitIso_hom_fac,
    cofibrantAlgebraHammockInclusionMap_normalization,
    ← Category.assoc, reducedColimitIso_hom_fac, MixedRelative.graphNormalization_reducedMap]
  rfl

lemma cofibrantAlgebraHammockInclusionMap_postcompose
    (X : (cofibrantAlgebraRelativeCategory A).category)
    {Y Z : (cofibrantAlgebraRelativeCategory A).category} (g : Y ⟶ Z) :
    reducedPostcomposeMap (cofibrantAlgebraRelativeCategory A).weakEquivalences X g ≫
        cofibrantAlgebraHammockInclusionMap A X Z =
      cofibrantAlgebraHammockInclusionMap A X Y ≫ algebraReducedHammockPostcompose A
        ((cofibrantAlgebraDKInclusion A).obj X) ((cofibrantAlgebraDKInclusion A).map g) := by
  let := modelCategory A
  rw [cofibrantAlgebraHammockInclusionMap_eq_mixed,
    cofibrantAlgebraHammockInclusionMap_eq_mixed]
  exact MixedRelative.reducedMap_postcompose (cofibrantAlgebraDKInclusionRelative A) X g

lemma cofibrantAlgebraHammockInclusionMap_precompose
    (Z : (cofibrantAlgebraRelativeCategory A).category)
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y) :
    reducedPrecomposeMap (cofibrantAlgebraRelativeCategory A).weakEquivalences Z f ≫
        cofibrantAlgebraHammockInclusionMap A X Z =
      cofibrantAlgebraHammockInclusionMap A Y Z ≫ algebraReducedHammockPrecompose A
        ((cofibrantAlgebraDKInclusion A).obj Z) ((cofibrantAlgebraDKInclusion A).map f) := by
  let := modelCategory A
  rw [cofibrantAlgebraHammockInclusionMap_eq_mixed,
    cofibrantAlgebraHammockInclusionMap_eq_mixed]
  exact MixedRelative.reducedMap_precompose (cofibrantAlgebraDKInclusionRelative A) Z f

end SerrePositivity.EInfinity.BarrattEccles
