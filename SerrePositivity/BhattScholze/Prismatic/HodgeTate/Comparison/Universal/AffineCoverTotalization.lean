module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoverCompleteTor
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoefficientSingleRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialComparison

/-!
# 元の affine 剰余行の結晶被覆への完備導来底変換と Tot

## 概要
Construction 6.1 の上界三を、元の affine 剰余加群を置いた離散行へ適用する。

## 方針
元の single 行の零の一様下界と、検証済みの有限完全 Tor 振幅による標準比較を使う。

## 規約
完備化座標は α(p), α(d) のままである。α(d) を p と置き換えず、
被覆上の元の剰余模型への同一視は別に必要となる。一般の結晶 HT 同型を使わない。

## 使われ方
Proposition 6.2 の標準完備底変換と元の Tot の比較。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion InfinityCategories HTComparisonTotal HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の affine 剰余の基底加群を、そのまま離散複体の余単体的行に置く。 -/
abbrev affineBaseSingleRows : CosimplicialObject (Complex A) :=
  coefficientSingleRows (affineBaseModules P hP r)

/-- 元の離散行は全て、同じ零のホモロジー下界を持つ。 -/
theorem affineBaseSingleRows_lowerBound (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero (((affineBaseSingleRows P hP r).obj ⦋n⦌).homology i) :=
  HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0
    ((affineBaseModules P hP r).obj ⦋n⦌) i (by omega)

/-- 元の剰余行での、指定された被覆への完備導来底変換–Tot 比較は同型。 -/
theorem affineCover_completedTotalComparison_isIso
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    IsIso (cosimplicialNativeCompletedBaseChangeComparison
      (Construction61.crystallineCoverMap P).toRingHom ![(p : A), P.generator]
      (affineBaseSingleRows P hP r) 0 (affineBaseSingleRows_lowerBound P hP r)) :=
  cosimplicialNativeCompletedBaseChangeComparison_isIso
    (Construction61.crystallineCoverMap P).toRingHom ![(p : A), P.generator] 3
    (Construction61.crystallineCoverMap_torAmplitude P hF hR)
    (affineBaseSingleRows P hP r) 0 (affineBaseSingleRows_lowerBound P hP r)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
