module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineOrdinaryRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineResolvedOrdinaryTotals

/-!
# 元の affine 結晶行への標準完備導来 Tot 比較

## 概要
元の標準完備導来底変換の Tot 比較を、同じ affine 終域行の Tot へ接続する。

## 方針
標準の半自由完備行から元の離散拡大行への指定同型と、元の通常係数射の自然同型を合成する。

## 規約
平坦性は係数射にだけ要求する。元の入力や Tot の K-flat 性を要求しない。

## 使われ方
特定の Zp 係数射へ Lemma 4.22 を適用して、元の Hodge–Tate 模型へ戻す。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.DifferentialGraded.ScalarExtension
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hPg : P.generator = (p : A)) (hQg : Q.generator = (p : B))
include hPg hQg

/-- 同じ標準半自由完備行の Tot から、元の affine 終域行の Tot への指定同型。 -/
def affineCrystallineResolvedTotalIso (hf : f.toRingHom.Flat) (r : ℕ) :
    DerivedCategory.Q.obj (cosimplicialTotal
      (resolvedCompletedBaseChange f.toRingHom (fun _ : Fin 1 => (p : A))
        (coefficientSingleRows (affineBaseModules P hP r)))) ≅
      DerivedCategory.Q.obj (cosimplicialTotal
        (coefficientSingleRows (affineBaseModules Q hQ r))) := by
  let M := affineBaseModules P hP r
  have hc (n : SimplexCategory) : IsModuleComplete B (f.toRingHom (p : A))
      ((ModuleCat.extendScalars f.toRingHom).obj (M.obj n)) := by
    simpa only [map_natCast] using
      affineCrystallineExtendedRow_complete f hP hQ hPg hQg r n
  let e := crystallineResolvedOrdinaryTotalIso f.toRingHom hf (p : A) M hc
  let a := Functor.isoWhiskerRight (affineCrystallineOrdinaryRowsIso f hP hQ hPg hQg r)
    (HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0)
  exact e ≪≫ DerivedCategory.Q.mapIso
    ((cochainProductTotalizationFunctor (ModuleCat.{u} B)).mapIso
      ((alternatingCofaceMapComplex (Complex B)).mapIso a))

/-- 元の標準完備導来底変換から元の affine 終域行の Tot へ向かう指定射。 -/
def affineCrystallineCompletedTotalComparison (hf : f.toRingHom.Flat) (r : ℕ) :
    (finiteDerivedCompletionFunctor (fun _ : Fin 1 => f.toRingHom (p : A))).obj
        ((complexDerivedExtension f.toRingHom).obj
          (DerivedCategory.Q.obj (cosimplicialTotal
            (coefficientSingleRows (affineBaseModules P hP r))))) ⟶
      DerivedCategory.Q.obj (cosimplicialTotal
        (coefficientSingleRows (affineBaseModules Q hQ r))) :=
  cosimplicialNativeCompletedBaseChangeComparison f.toRingHom
      (fun _ : Fin 1 => (p : A)) (coefficientSingleRows (affineBaseModules P hP r)) 0
      (coefficientSingleRows_lowerBound (affineBaseModules P hP r)) ≫
    (affineCrystallineResolvedTotalIso f hP hQ hPg hQg hf r).hom

/-- 元の完全 Tor 条件の下で、同じ指定された完備導来 Tot 比較は同型。 -/
theorem affineCrystallineCompletedTotalComparison_isIso (hf : f.toRingHom.Flat) (r c : ℕ)
    (hc : HasCochainCompleteTorAmplitude f.toRingHom (fun _ : Fin 1 => (p : A)) c) :
    IsIso (affineCrystallineCompletedTotalComparison f hP hQ hPg hQg hf r) := by
  haveI := cosimplicialNativeCompletedBaseChangeComparison_isIso f.toRingHom
    (fun _ : Fin 1 => (p : A)) c hc (coefficientSingleRows (affineBaseModules P hP r)) 0
    (coefficientSingleRows_lowerBound (affineBaseModules P hP r))
  dsimp only [affineCrystallineCompletedTotalComparison]
  infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
