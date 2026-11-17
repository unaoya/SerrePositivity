module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.UnboundedBoundedModuleBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverResolvedTotal
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoverCompletionCoordinates
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionDerived
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialComparison

/-!
# 元の分解行から上に有界な完備底変換への比較

## 概要
元の剰余行の半自由分解の完備像を、元の上に有界な二座標底変換へ同定する。

## 方針
元の座標比較、同じ半自由模型の計算同型、同じ加群の射影分解による比較を合成する。

## 規約
κや指定した剰余行の被覆同型から逆算して同型を定めない。

## 使われ方
HT04.R1の指定された項ごとの写像の始域を固定する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonTotal
open HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完備化前の同じ半自由行と、同じ加群の上に有界な導来底変換の比較。 -/
def affineResolvedRowUncompletedSourceIso
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    let α := (Construction61.crystallineCoverMap P).toRingHom
    let M := (affineBaseModules P hP r).obj n
    let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
    DerivedCategory.Q.obj (baseChange α ((complexResolutionFunctor A).obj K)) ≅
      ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj := by
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let M := (affineBaseModules P hP r).obj n
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  let ε : (complexResolutionFunctor A).obj K ⟶ K := (complexResolutionAugmentation A).app K
  exact (nativeDerivedScalarModelIso α ε (complexResolutionAugmentation_quasiIso A K)
    (complexResolutionFunctor_kFlat A K)).symm ≪≫ unboundedBoundedModuleBaseChangeIso α M

/-- 元の剰余行の指定された半自由模型を、同じ上に有界な完備底変換へ移す。 -/
def affineResolvedRowBoundedSourceIso
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    DerivedCategory.Q.obj ((resolvedCompletedBaseChange
      (Construction61.crystallineCoverMap P).toRingHom ![(p : A), P.generator]
      (coefficientSingleRows (affineBaseModules P hP r))).obj n) ≅
    (pairCompletedBaseChange (Construction61.crystallineCoverMap P).toRingHom
      (p : Construction61.crystallineCoverRing P) (p : Construction61.crystallineCoverRing P)
      (boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n))).obj := by
  let B := Construction61.crystallineCoverRing P
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let M := (affineBaseModules P hP r).obj n
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  let F := finiteDerivedCompletionFunctor (fun _ : Fin 2 => (p : B))
  exact (coverImageCompletionNatIso P).app ((complexResolutionFunctor A).obj K) ≪≫
    (finiteDerivedCompletionComparison (fun _ : Fin 2 => (p : B))).symm.app
      (baseChange α ((complexResolutionFunctor A).obj K)) ≪≫
    F.mapIso (affineResolvedRowUncompletedSourceIso P hP r n)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
