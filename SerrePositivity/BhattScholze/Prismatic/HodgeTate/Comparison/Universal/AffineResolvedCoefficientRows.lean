module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedBaseRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoefficientSingleRows

/-!
# 元の向き付き係数射による指定された半自由完備行の射

## 概要
元の余単体的剰余係数射を、指定された半自由行の完備係数拡大から終域の完備行へ写す。

## 方針
同じ半自由増大、元のsingleと係数拡大の同型、随伴で延長した元の係数射を合成する。

## 規約
自然性は厳密な複体の図式上で証明する。この段階で各行の擬同型性は仮定しない。

## 使われ方
HT04.R1で項ごとの指定同型と比較する、元の標準の行射。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 元の剰余係数射から得られる、通常の係数拡大後のsingle行の射。 -/
def affineAnyExtendedSingleRowsMap :
    coefficientSingleRows (affineBaseModules P hP r) ⋙
        (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ) ⟶
      coefficientSingleRows (affineBaseModules Q hQ r) :=
  (coefficientExtendedSingleRowsIso f.toRingHom (affineBaseModules P hP r)).hom ≫
    Functor.whiskerRight (affineBaseAnyOrdinaryCoefficientMap f hP hQ r)
      (HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0)

/-- 元の半自由増大と係数射を同じ完備化へ通した、厳密な余単体的行の射。 -/
def affineResolvedCompletedRowsMap {s : ℕ} (x : Fin s → A) :
    resolvedCompletedBaseChange f.toRingHom x (coefficientSingleRows (affineBaseModules P hP r)) ⟶
      coefficientSingleRows (affineBaseModules Q hQ r) ⋙
        finiteCompletionFunctor (fun j => f.toRingHom (x j)) :=
  crystallineResolvedCompletedAugmentation f.toRingHom x
      (coefficientSingleRows (affineBaseModules P hP r)) ≫
    Functor.whiskerRight (affineAnyExtendedSingleRowsMap f hP hQ r)
      (finiteCompletionFunctor (fun j => f.toRingHom (x j)))

/-- 指定行射の各成分は、元の増大と元の係数射の合成を完備化したもの。 -/
theorem affineResolvedCompletedRowsMap_app {s : ℕ} (x : Fin s → A) (n : SimplexCategory) :
    (affineResolvedCompletedRowsMap f hP hQ r x).app n =
      (finiteCompletionFunctor (fun j => f.toRingHom (x j))).map
        (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map
            ((resolvedCosimplicialAugmentation
              (coefficientSingleRows (affineBaseModules P hP r))).app n) ≫
          (affineAnyExtendedSingleRowsMap f hP hQ r).app n) := by
  simp only [affineResolvedCompletedRowsMap, crystallineResolvedCompletedAugmentation,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
