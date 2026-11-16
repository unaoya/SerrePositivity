module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineRowBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCompletedCoefficientIsomorphism
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CompletedCoefficientMap

/-!
# 元の結晶 affine 行の標準完備係数変更

## 概要
元の affine 剰余行の間の標準完備係数変更が、各次数で同型になることを示す。

## 方針
指定された通常の代数同型とその純テンソル上の値を、元の標準延長の同型判定へ渡す。

## 規約
両基底の選択生成元は p とする。元の行の導来完備性を使い、別の比較射を選ばない。

## 使われ方
特定の Zp 係数射の完備導来底変換を、元の affine 剰余行へ接続する。
-/

public noncomputable section
universe u
open CategoryTheory
open SerrePositivity.Cosimplicial SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hPg : P.generator = (p : A)) (hQg : Q.generator = (p : B))

/-- 元の標準完備係数変更は、結晶的な affine 剰余模型の各行で同型。 -/
theorem affineCrystallineCompletedCoefficientMap_app_isIso (r : ℕ) (n : SimplexCategory) :
    letI := f.toRingHom.toAlgebra
    IsIso ((affineBaseCompletedCoefficientMap hP r f hQ
      (crystallineCoefficientGenerator_eq f hPg hQg)).app n) := by
  letI := f.toRingHom.toAlgebra
  let X := reducedModel P hP r
  let Y := reducedModel Q hQ r
  let ιX := affineBaseCoefficients P hP r
  let ιY := affineBaseCoefficients Q hQ r
  let g := affineHTCoefficientReduced f hP hQ r (crystallineCoefficientGenerator_eq f hPg hQg)
  let hι := affineBaseCoefficient_square hP r f hQ (crystallineCoefficientGenerator_eq f hPg hQg)
  letI : Algebra A (X.obj n) := (ιX.app n).hom.toAlgebra
  letI : Algebra B (Y.obj n) := (ιY.app n).hom.toAlgebra
  letI : Algebra A (Y.obj n) := ((ιY.app n).hom.comp (algebraMap A B)).toAlgebra
  letI := SerrePositivity.Cosimplicial.scalarTower A B Y ιY n
  obtain ⟨e, he⟩ := exists_affineCrystallineRowBaseChangeEquiv f hP hQ hPg hQg r n
  change IsIso (pointwiseCompletedAlgMap p A B (X.obj n) (Y.obj n)
    (affineBaseModules_complete Q hQ r n)
    (SerrePositivity.Cosimplicial.coefficientAlgHom A B X Y ιX ιY g hι n))
  exact affinePointwiseCompletedAlgMap_isIso p A B (X.obj n) (Y.obj n)
    (affineBaseModules_complete Q hQ r n)
    (SerrePositivity.Cosimplicial.coefficientAlgHom A B X Y ιX ιY g hι n) e he

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
