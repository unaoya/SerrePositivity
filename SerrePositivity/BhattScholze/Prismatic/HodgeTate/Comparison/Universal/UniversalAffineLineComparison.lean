module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeCoverHomologySquares
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverFormalVanishing
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryEtaQuasiIso
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineRestrictedResolvedCriterion
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverTargetAugmentation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.UniversalCrystallineHodgeTate

/-!
# 普遍向き付き基底上の元の affine line の HT 加群比較

## 概要
Proposition 6.2 の証明の (ii) における普遍向き付き基底で、元の零次・一次の
標準 HT 写像の全単射性と高次の消滅へ戻す。

## 方針
HT03 の特定の普遍結晶被覆の計算を、同じ元のηの通常被覆像の擬同型性へ渡す。
元の指定増大の比較と完備性による反映を使い、元の基底の終点へ降下する。

## 規約
一般の結晶の比較は入力にしない。元の終点・同じη・指定された完備被覆模型を保つ。
任意の有界 prism、多変数、層の比較へ拡張したという主張ではない。

## 使われ方
HT04.R3 の終点。HT05・HT06 へはここから進まない。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ) [Fact p.Prime]

/-- 特定の普遍結晶被覆の計算から、同じ元のηの指定完備被覆像が擬同型となる。 -/
theorem universalOrientedPrism_affineLine_resolvedCover_quasiIso
    (η : affineLineFormalModel (universalOrientedPrism.{u} p) ⟶ affineHTTotalComplex (universalOrientedPrism.{u} p) (universalOrientedPrism_bounded.{u} p) 1)
    (h0 : (affineLineFormalZeroIso (universalOrientedPrism.{u} p)).hom ≫ homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap (universalOrientedPrism.{u} p) (universalOrientedPrism_bounded.{u} p) 1 0))
    (h1 : (affineLineFormalOneIso (universalOrientedPrism.{u} p)).hom ≫ homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap (universalOrientedPrism.{u} p) (universalOrientedPrism_bounded.{u} p) 1 1)) :
    QuasiIso ((Construction61.completedCoverModelFunctor (universalOrientedPrism.{u} p)).map
      ((complexResolutionFunctor (UniversalOrientedPrismRing.{u} p)).map
        ((affineRestrictedComplexFunctor (universalOrientedPrism.{u} p) 1).map η))) := by
  have ho := affineOrdinaryEta_quasiIso (Construction61.crystallineCoverMap (universalOrientedPrism.{u} p)) (universalOrientedPrism_bounded.{u} p)
    (Construction61.crystallineCover_bounded (universalOrientedPrism.{u} p))
    (Construction61.crystallineCover_generator (universalOrientedPrism.{u} p))
    (HTUniversalCrystallineInput.universalCrystallineCover_hodgeTate_iso p 1) η h0 h1
  apply affineLine_resolvedCover_quasiIso_of_ordinary (universalOrientedPrism.{u} p) (universalOrientedPrism_bounded.{u} p)
    (universalOrientedPrism_frobenius_isCompletelyFlat p)
    (universalOrientedPrism_mod_generator_p_regular p) η
  simpa only [affineOrdinaryCoverFunctor, Functor.comp_map] using ho

/-- 普遍向き付き基底上で、元の affine line の標準 HT 写像による元の加群比較。 -/
theorem universalOrientedPrism_affineLine_moduleComparison :
    Function.Bijective (hodgeTateMapZero (universalOrientedPrism.{u} p) (universalOrientedPrism_bounded.{u} p) 1) ∧
      Function.Bijective (hodgeTateMapOne (universalOrientedPrism.{u} p) (universalOrientedPrism_bounded.{u} p) 1) ∧
      ∀ i : ℕ, 1 < i → Subsingleton (hodgeTateCohomology' (universalOrientedPrism.{u} p) (universalOrientedPrism_bounded.{u} p) 1 i) := by
  obtain ⟨η, h0, h1⟩ := exists_affineLine_HT_realization (universalOrientedPrism.{u} p) (universalOrientedPrism_bounded.{u} p)
  have hf := universalOrientedPrism_affineLine_resolvedCover_quasiIso.{u} p η h0 h1
  have hres := affineLine_moduleComparison_of_restrictedResolvedCover.{u}
    (universalOrientedPrism.{u} p) (universalOrientedPrism_bounded.{u} p)
    (universalOrientedPrism_frobenius_isCompletelyFlat.{u} p)
    (universalOrientedPrism_mod_generator_p_regular.{u} p) η h0 h1 hf
  exact hres

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
