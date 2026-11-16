module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineOrdinaryRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CosimplicialComparison

/-!
# 元の affine 基底複体の平坦なコホモロジー係数変更

## 概要
元の affine 剰余模型の通常係数拡大を、元の基底複体とそのホモロジーで比較する。

## 方針
元の自然な行同型と交代余面複体の標準同型を合成し、平坦な係数拡大のホモロジー同型を使う。

## 規約
同じ係数写像の行同型を使う。HT 写像の全単射性を仮定しない。

## 使われ方
特定の Zp 係数射の標準 HT 写像を、元のコホモロジーの係数変更で照合する。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open HTComparisonTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hPg : P.generator = (p : A)) (hQg : Q.generator = (p : B))

/-- 元の affine 剰余模型を、元の基底環上の交代余面複体として読む。 -/
abbrev affineBaseComplex (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat.{u} A)).obj (affineBaseModules P hP r)

include hPg hQg
/-- 元の通常係数射の行同型は、同じ交代余面複体の同型を与える。 -/
def affineCrystallineBaseComplexIso (r : ℕ) :
    ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℕ)).obj
        (affineBaseComplex P hP r) ≅ affineBaseComplex Q hQ r :=
  (alternatingCofaceFunctorIso (ModuleCat.extendScalars f.toRingHom)).app
      (affineBaseModules P hP r) ≪≫
    (alternatingCofaceMapComplex (ModuleCat.{u} B)).mapIso
      (affineCrystallineOrdinaryRowsIso f hP hQ hPg hQg r)

/-- 平坦な係数射では、同じ基底複体のホモロジーも元の係数拡大と可換。 -/
def affineCrystallineBaseCohomologyIso (hf : f.toRingHom.Flat) (r i : ℕ) :
    (ModuleCat.extendScalars f.toRingHom).obj ((affineBaseComplex P hP r).homology i) ≅
      (affineBaseComplex Q hQ r).homology i := by
  let F := ModuleCat.extendScalars f.toRingHom
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (((affineBaseComplex P hP r).sc i).mapHomologyIso F).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) i).mapIso
      (affineCrystallineBaseComplexIso f hP hQ hPg hQg r)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
