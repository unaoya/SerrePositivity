module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.ResolvedCoverReflection

/-!
# 元の射を指定半自由模型の結晶被覆で検出する

## 概要
普遍向き付き基底上の元の完備複体間の射を、HT02 の指定半自由分解関手で計算した被覆像で検出する。

## 方針
元の増大の自然性と擬同型性で、既存の半自由模型上の Construction 6.1 の反映を元の射へ戻す。

## 規約
元の source・target の p・d 完備性を明示する。元の複体の K-flat 性は仮定しない。

## 使われ方
元の affine line の標準 η の実現を、具体的な結晶被覆上の比較で検出する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open SerrePositivity.DerivedCompletion HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime]
variable {K L : CochainComplex (ModuleCat.{u} (UniversalOrientedPrismRing.{u} p)) ℤ}

/-- 元の完備な射は、指定半自由分解の結晶被覆像の擬同型性から検出できる。 -/
theorem universal_quasiIso_of_resolvedCover_map_quasiIso (f : K ⟶ L)
    (hpK : IsComplete (UniversalOrientedPrismRing.{u} p) (p : UniversalOrientedPrismRing.{u} p)
      (DerivedCategory.Q.obj K))
    (hpL : IsComplete (UniversalOrientedPrismRing.{u} p) (p : UniversalOrientedPrismRing.{u} p)
      (DerivedCategory.Q.obj L))
    (hdK : IsComplete (UniversalOrientedPrismRing.{u} p) (universalOrientedPrism.{u} p).generator
      (DerivedCategory.Q.obj K))
    (hdL : IsComplete (UniversalOrientedPrismRing.{u} p) (universalOrientedPrism.{u} p).generator
      (DerivedCategory.Q.obj L))
    (hf : QuasiIso ((Construction61.completedCoverModelFunctor (universalOrientedPrism.{u} p)).map
      ((complexResolutionFunctor (UniversalOrientedPrismRing.{u} p)).map f))) : QuasiIso f :=
  quasiIso_of_resolvedCover_map_quasiIso (universalOrientedPrism.{u} p)
    (universalOrientedPrism_frobenius_isCompletelyFlat p)
    (universalOrientedPrism_mod_generator_p_regular p) f hpK hpL hdK hdL hf

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
