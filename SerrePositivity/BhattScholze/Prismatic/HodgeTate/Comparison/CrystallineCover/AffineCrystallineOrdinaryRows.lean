module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineCompletedRows
public import SerrePositivity.HomologicalAlgebra.AlgebraScalarExtensionModule
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra

/-!
# 元の結晶 affine 行の通常係数拡大と完備性

## 概要
元の affine 行の通常係数拡大が完備であることと、標準完備係数射の単位から来る自然な同型を示す。

## 方針
元の代数同型を元の加群の係数拡大へ移し、元の標準単位と既存の完備係数射を合成する。

## 規約
元の基底作用と元の標準係数変更を使う。単位の逆鎖写像は選ばない。

## 使われ方
特定の Zp 係数射に沿う元の離散行を、同じ完備導来係数変更の Tot と結ぶ。
-/

public noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hPg : P.generator = (p : A)) (hQg : Q.generator = (p : B))
include hQ hPg hQg

/-- 元の通常係数拡大の行と元の affine 終域行の同じ基底作用上の同型。 -/
def affineCrystallineExtendedRowIso (r : ℕ) (n : SimplexCategory) :
    (ModuleCat.extendScalars f.toRingHom).obj ((affineBaseModules P hP r).obj n) ≅
      (affineBaseModules Q hQ r).obj n := by
  letI := f.toRingHom.toAlgebra
  letI : Algebra A ((reducedModel P hP r).obj n) :=
    ((affineBaseCoefficients P hP r).app n).hom.toAlgebra
  letI : Algebra B ((reducedModel Q hQ r).obj n) :=
    ((affineBaseCoefficients Q hQ r).app n).hom.toAlgebra
  let e := (exists_affineCrystallineRowBaseChangeEquiv f hP hQ hPg hQg r n).choose
  exact algebraScalarExtensionModuleIso A B ((affineBaseModules P hP r).obj n) ≪≫
    e.toLinearEquiv.toModuleIso

/-- 元の通常係数拡大後の各行も、終域の p 作用について導来完備。 -/
theorem affineCrystallineExtendedRow_complete (r : ℕ) (n : SimplexCategory) :
    IsModuleComplete B (p : B)
      ((ModuleCat.extendScalars f.toRingHom).obj ((affineBaseModules P hP r).obj n)) :=
  isModuleComplete_of_linearEquiv B (p : B) _ _
    (affineCrystallineExtendedRowIso f hP hQ hPg hQg r n).toLinearEquiv.symm
    (affineBaseModules_complete Q hQ r n)

/-- 元の完備化単位から元の完備係数射へ進む、通常係数拡大後の自然な射。 -/
def affineCrystallineOrdinaryCoefficientMap (r : ℕ) :
    affineBaseModules P hP r ⋙ ModuleCat.extendScalars f.toRingHom ⟶
      affineBaseModules Q hQ r := by
  letI := f.toRingHom.toAlgebra
  exact Functor.whiskerLeft (affineBaseModules P hP r ⋙ ModuleCat.extendScalars f.toRingHom)
      (moduleCompletionH0Unit B (p : B)) ≫
    affineBaseCompletedCoefficientMap hP r f hQ (crystallineCoefficientGenerator_eq f hPg hQg)

/-- 元の単位と標準係数射から作った同じ通常係数射は、各行で同型。 -/
theorem affineCrystallineOrdinaryCoefficientMap_app_isIso (r : ℕ) (n : SimplexCategory) :
    IsIso ((affineCrystallineOrdinaryCoefficientMap f hP hQ hPg hQg r).app n) := by
  letI := f.toRingHom.toAlgebra
  haveI := moduleCompletionH0Unit_isIso_of_complete B (p : B)
    ((ModuleCat.extendScalars f.toRingHom).obj ((affineBaseModules P hP r).obj n))
    (affineCrystallineExtendedRow_complete f hP hQ hPg hQg r n)
  haveI := affineCrystallineCompletedCoefficientMap_app_isIso f hP hQ hPg hQg r n
  change IsIso (((moduleCompletionH0Unit B (p : B)).app
    ((ModuleCat.extendScalars f.toRingHom).obj ((affineBaseModules P hP r).obj n))) ≫ _)
  infer_instance

/-- 同じ元の通常係数射を束ねた、元の余単体的加群の自然な同型。 -/
def affineCrystallineOrdinaryRowsIso (r : ℕ) :
    affineBaseModules P hP r ⋙ ModuleCat.extendScalars f.toRingHom ≅
      affineBaseModules Q hQ r :=
  NatIso.ofComponents (fun n => by
    haveI := affineCrystallineOrdinaryCoefficientMap_app_isIso f hP hQ hPg hQg r n
    exact asIso ((affineCrystallineOrdinaryCoefficientMap f hP hQ hPg hQg r).app n))
    (by
      intro m n θ
      exact (affineCrystallineOrdinaryCoefficientMap f hP hQ hPg hQg r).naturality θ)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
