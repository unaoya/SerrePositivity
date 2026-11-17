module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalTotalModel

/-!
# 元の HT 全複体からの指定された被覆–Tot 比較

## 概要
元の完備多項式線形 HT 全複体を基底へ制限したものに、被覆への標準完備導来底変換–Tot 比較を接続する。

## 方針
元の離散行の Tot への指定同型の逆を、実際の導来係数拡大と像の二座標完備化で写す。

## 規約
行の像を終域の元の剰余行へ同一視する段階は残る。一般結晶 HT 比較を入力にしない。

## 使われ方
元の η の終域の被覆像と、HT02 が計算する完備行の Tot の接続。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded.ScalarExtension DifferentialGraded DerivedCompletion InfinityCategories HTComparisonTotal HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の指定 HT 全複体から、元の被覆上の完備行の Tot への標準比較。 -/
def affineOriginalCoverTotalComparison :
    (finiteDerivedCompletionFunctor
        (fun j => (Construction61.crystallineCoverMap P).toRingHom (![(p : A), P.generator] j))).obj
      ((complexDerivedExtension (Construction61.crystallineCoverMap P).toRingHom).obj
        (DerivedCategory.Q.obj (affineComplexOnBase P r (affineHTTotalComplex P hP r)))) ⟶
      DerivedCategory.Q.obj (cosimplicialTotal (resolvedCompletedBaseChange
        (Construction61.crystallineCoverMap P).toRingHom ![(p : A), P.generator]
        (affineBaseSingleRows P hP r))) :=
  (finiteDerivedCompletionFunctor
      (fun j => (Construction61.crystallineCoverMap P).toRingHom (![(p : A), P.generator] j))).map
    ((complexDerivedExtension (Construction61.crystallineCoverMap P).toRingHom).map
      (DerivedCategory.Q.map (affineBaseSingleTotalPolynomialIso P hP r).inv)) ≫
    cosimplicialNativeCompletedBaseChangeComparison (Construction61.crystallineCoverMap P).toRingHom
      ![(p : A), P.generator] (affineBaseSingleRows P hP r) 0
      (affineBaseSingleRows_lowerBound P hP r)

/-- 元の指定 HT 全複体での同じ標準比較は、Construction 6.1 の入力の下で同型。 -/
theorem affineOriginalCoverTotalComparison_isIso
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    IsIso (affineOriginalCoverTotalComparison P hP r) := by
  haveI := affineCover_completedTotalComparison_isIso P hP r hF hR
  dsimp only [affineOriginalCoverTotalComparison]
  infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
