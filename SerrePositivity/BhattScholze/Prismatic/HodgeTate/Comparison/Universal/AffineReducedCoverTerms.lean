module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.PairScalarConeCompatibility
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.ScalarConeOrientation
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 元の剰余行の被覆への完備導来底変換

## 概要
元の affine 剰余行の二座標完備導来底変換を、被覆上の元の affine 剰余行へ同定する。

## 方針
元の full envelope の正則商の錐、完備底変換の錐比較、α(d)=p*u の鎖同型を合成する。

## 規約
これは項ごとの指定同型である。余単体射への自然性と元の標準写像の照合は別に確認する。

## 使われ方
元の被覆–Tot 比較の終域の完備行を、元の結晶被覆の剰余模型へ戻す。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 零次数加群上でも、向きの単位を元の錐の比較に残す。 -/
def derivedScalarConeOrientationSingleIso (a : R) (v : Rˣ) (M : ModuleCat.{u} R) :
    (derivedScalarConeFunctor R (a * (v : R))).obj ((moduleObjectFunctor R).obj M) ≅
      (derivedScalarConeFunctor R a).obj ((moduleObjectFunctor R).obj M) :=
  (derivedScalarConeComparison R (a * (v : R))).app ((CochainComplex.singleFunctor _ 0).obj M) ≪≫
    DerivedCategory.Q.mapIso (scalarConeOrientationIso a v ((CochainComplex.singleFunctor _ 0).obj M)) ≪≫
    (derivedScalarConeComparison R a).symm.app ((CochainComplex.singleFunctor _ 0).obj M)

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の剰余行の完備導来底変換は、元の結晶被覆の剰余行を計算する。 -/
def affineReducedCoverTermIso (n : SimplexCategory) :
    (pairCompletedBaseChange (Construction61.crystallineCoverMap P).toRingHom
      (p : Construction61.crystallineCoverRing P) (p : Construction61.crystallineCoverRing P)
      (boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n))).obj ≅
        (moduleObjectFunctor (Construction61.crystallineCoverRing P)).obj
          ((affineBaseModules (Construction61.crystallineCover P)
            (Construction61.crystallineCover_bounded P) r).obj n) := by
  let B := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let X := boundedAboveDerivedSingleFunctor.obj ((affineFullBaseModules P hP r).obj n)
  let M := (affineFullBaseModules Q hQ r).obj n
  let G := boundedAboveDerivedBaseChange α ⋙ boundedAboveDerivedCompletionFunctor B (p : B) ⋙
    boundedAboveDerivedCompletionFunctor B (p : B)
  let eR : (boundedAboveDerivedScalarCone A P.generator).obj X ≅
      boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n) :=
    ObjectProperty.isoMk _ (affineReducedScalarConeIso P hP r n)
  let v := (Construction61.crystallineCoverMap P).existsUnique_generator_unit.choose
  have hv : α P.generator = (p : B) * (v : B) := by
    exact (Construction61.crystallineCoverMap P).existsUnique_generator_unit.choose_spec.1
  exact (DerivedCategory.Minus.ι.mapIso (G.mapIso eR)).symm ≪≫
    pairCompletedScalarConeIso α P.generator (p : B) (p : B) X ≪≫
    (derivedScalarConeFunctor B (α P.generator)).mapIso (affineFullCoverTermIso P hP r n) ≪≫
    eqToIso (congrArg (fun b => (derivedScalarConeFunctor B b).obj ((moduleObjectFunctor B).obj M)) hv) ≪≫
    derivedScalarConeOrientationSingleIso (p : B) v M ≪≫
    affineReducedScalarConeIso Q hQ r n

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
